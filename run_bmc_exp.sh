#!/bin/bash
#
# BMC 批量实验脚本
# 对 benchmark 目录下所有 .btor2 文件运行 bmc，支持可调并行度
#
# 用法:
#   ./run_bmc_exp.sh [并行度] [iteration] [最大frame] [find_unsat] [find_sat]
#
# 示例:
#   ./run_bmc_exp.sh          # 默认并行度 10
#   ./run_bmc_exp.sh 20       # 并行度 20
#   ./run_bmc_exp.sh 10 300 15 300 1  # 自定义所有参数
#

set -o pipefail

# ==================== 可配置参数 ====================

# 并行度（第一个命令行参数，默认 10）
PARALLEL=${1:-10}

# BMC 参数（命令行参数 2-6，带默认值）
ITERATION=${2:-100}
MAX_BOUND=${3:-30}
FIND_UNSAT=${4:-20}
FIND_SAT=${5:-1}

# 路径配置
BMC_BIN="/home/jiongming/desktop/FORWORD/build/bmc"                                                  # bmc 可执行文件
BENCHMARK_DIR="/home/jiongming/desktop/forword_exp/benchmark_fixed" # 测试用例目录
LOG_DIR="/home/jiongming/desktop/forword_exp/3"                         # 日志输出目录

# ==================== 初始化 ====================

mkdir -p "$LOG_DIR"

if ! [[ "$MAX_BOUND" =~ ^[1-9][0-9]*$ ]]; then
    echo "[ERROR] 最大frame必须是大于等于1的整数，当前值: $MAX_BOUND" >&2
    exit 2
fi

# 统计信息
TOTAL=$(find "$BENCHMARK_DIR" -name "*.btor2" -type f | wc -l)
PASS_FILE="$LOG_DIR/.pass_count"
FAIL_FILE="$LOG_DIR/.fail_count"
echo 0 > "$PASS_FILE"
echo 0 > "$FAIL_FILE"

# ==================== 单个任务执行函数 ====================

run_bmc() {
    local btor2_file="$1"

    # 生成日志文件名：用相对路径，斜杠替换为下划线
    local rel_path="${btor2_file#$BENCHMARK_DIR/}"
    local case_name="${rel_path%.btor2}"
    local case_name_clean="${case_name//\//_}"
    local log_file="$LOG_DIR/${case_name_clean}.log"

    local frame frame_log exit_code case_status="PASS" stop_frame=0

    : > "$log_file"
    echo "[$(date '+%Y-%m-%d %H:%M:%S')] Starting: $case_name_clean (frames 1..$MAX_BOUND)" | tee -a "$log_file"

    # 当前 bmc 只检查指定 bound，因此逐帧运行。首次发现反例或工具错误即停止。
    for ((frame = 1; frame <= MAX_BOUND; frame++)); do
        frame_log="${log_file}.frame_${frame}.tmp"
        echo "===== FRAME $frame / $MAX_BOUND =====" | tee -a "$log_file"

        "$BMC_BIN" --file "$btor2_file" \
            --iteration "$ITERATION" \
            --bound "$frame" \
            --find_unsat "$FIND_UNSAT" \
            --find_sat "$FIND_SAT" \
            2>&1 | tee "$frame_log" | tee -a "$log_file"

        exit_code=${PIPESTATUS[0]}

        if [ "$exit_code" -ne 0 ]; then
            case_status="ERROR"
            stop_frame=$frame
            echo "CASE_RESULT: ERROR at frame $frame (exit=$exit_code)" | tee -a "$log_file"
            break
        elif grep -q '^\[RESULT\] Failed at bound ' "$frame_log"; then
            case_status="VIOLATION"
            stop_frame=$frame
            echo "CASE_RESULT: VIOLATION at frame $frame" | tee -a "$log_file"
            break
        elif ! grep -q "^\[RESULT\] Bound $frame passed\." "$frame_log"; then
            case_status="ERROR"
            stop_frame=$frame
            echo "CASE_RESULT: ERROR at frame $frame (missing recognized result)" | tee -a "$log_file"
            break
        fi

        rm -f "$frame_log"
    done

    rm -f "${log_file}.frame_"*.tmp

    if [ "$case_status" = "PASS" ]; then
        echo "CASE_RESULT: PASS through frame $MAX_BOUND" | tee -a "$log_file"
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] PASS: $case_name_clean (frames 1..$MAX_BOUND)"
        # 原子递增通过计数
        (
            flock -x 200
            cnt=$(cat "$PASS_FILE")
            echo $((cnt + 1)) > "$PASS_FILE"
        ) 200>"$LOG_DIR/.counter_lock"
    else
        echo "[$(date '+%Y-%m-%d %H:%M:%S')] FAIL ($case_status at frame $stop_frame): $case_name_clean"
        (
            flock -x 200
            cnt=$(cat "$FAIL_FILE")
            echo $((cnt + 1)) > "$FAIL_FILE"
        ) 200>"$LOG_DIR/.counter_lock"
    fi

    [ "$case_status" = "PASS" ]
}

# 导出函数和变量供 xargs 子进程使用
export -f run_bmc
export BMC_BIN BENCHMARK_DIR LOG_DIR ITERATION MAX_BOUND FIND_UNSAT FIND_SAT PASS_FILE FAIL_FILE

# ==================== 打印实验配置 ====================

echo "============================================"
echo "  BMC 批量实验"
echo "============================================"
echo "  BMC binary:    $BMC_BIN"
echo "  Benchmark dir: $BENCHMARK_DIR"
echo "  Log dir:       $LOG_DIR"
echo "  Test cases:    $TOTAL"
echo "  Parallelism:   $PARALLEL"
echo "  Iteration:     $ITERATION"
echo "  Frames:        1..$MAX_BOUND"
echo "  Find unsat:    $FIND_UNSAT"
echo "  Find sat:      $FIND_SAT"
echo "============================================"
echo ""

START_TIME=$(date +%s)

# ==================== 并行执行 ====================

find "$BENCHMARK_DIR" -name "*.btor2" -type f | sort | \
    xargs -P "$PARALLEL" -I {} bash -c 'run_bmc "$@"' _ {}

# ==================== 结果汇总 ====================

END_TIME=$(date +%s)
ELAPSED=$((END_TIME - START_TIME))
PASS_CNT=$(cat "$PASS_FILE")
FAIL_CNT=$(cat "$FAIL_FILE")

echo ""
echo "============================================"
echo "  实验完成"
echo "============================================"
echo "  总用例数:     $TOTAL"
echo "  通过:         $PASS_CNT"
echo "  失败:         $FAIL_CNT"
echo "  耗时:         ${ELAPSED}s ($((ELAPSED / 60))m $((ELAPSED % 60))s)"
echo "  日志目录:     $LOG_DIR"
echo "============================================"

# 列出失败的用例
if [ "$FAIL_CNT" -gt 0 ]; then
    echo ""
    echo "失败用例列表:"
    grep -l '^CASE_RESULT: \(VIOLATION\|ERROR\)' "$LOG_DIR"/*.log 2>/dev/null | while read f; do
        basename "$f" .log
    done
fi

# 清理临时文件
rm -f "$PASS_FILE" "$FAIL_FILE" "$LOG_DIR/.counter_lock"
