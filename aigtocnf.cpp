#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <memory>
#include <algorithm>
#include <cstdlib>
#include <cstring>
#include <cstdio>
#include <limits>

extern "C" {
#include "aiger.h"
}

class AigToCnfConverter {
private:
    int verbose = 0;
    bool nocoi = false;
    bool nopg = false;
    bool noxor = false;
    bool noite = false;
    bool prtmap = false;

    void msg(const std::string &fmt) {
        if (verbose) {
            std::cerr << "[aigtocnf] " << fmt << std::endl;
        }
    }

    void wrn(const std::string &fmt) {
        std::fflush(stdout);
        std::cerr << "[aigtocnf] WARNING " << fmt << std::endl;
    }

    [[noreturn]] void die(const std::string &fmt) {
        std::fflush(stdout);
        std::cerr << "*** [aigtocnf] " << fmt << std::endl;
        std::exit(1);
    }

    bool have_same_variable(unsigned a, unsigned b) {
        return aiger_strip(a) == aiger_strip(b);
    }

    bool distinct_variables(unsigned a, unsigned b, unsigned c) {
        if (aiger_strip(a) == aiger_strip(b))
            return 0;
        if (aiger_strip(a) == aiger_strip(c))
            return 0;
        if (aiger_strip(b) == aiger_strip(c))
            return 0;
        return 1;
    }

    bool is_xor(aiger *aiger, unsigned lit, unsigned *rhs0ptr, unsigned *rhs1ptr) {
        aiger_and *and, *left, *right;
        unsigned left_rhs0, left_rhs1;
        unsigned right_rhs0, right_rhs1;
        unsigned not_right_rhs0, not_right_rhs1;
        
        and = aiger_is_and(aiger, lit);
        if (!and)
            return false;
        if (!aiger_sign(and->rhs0))
            return false;
        if (!aiger_sign(and->rhs1))
            return false;
        
        left = aiger_is_and(aiger, and->rhs0);
        if (!left)
            return false;
        right = aiger_is_and(aiger, and->rhs1);
        if (!right)
            return false;
            
        left_rhs0 = left->rhs0, left_rhs1 = left->rhs1;
        right_rhs0 = right->rhs0, right_rhs1 = right->rhs1;
        not_right_rhs0 = aiger_not(right_rhs0);
        not_right_rhs1 = aiger_not(right_rhs1);
        
        //      (!l0 | !l1) & (!r0 | !r1)
        // (A): ( r0 |  r1) & (!r0 | !r1)
        // (B): ( r1 |  r0) & (!r0 | !r1)
        //        r0 ^  r1                 // used
        //        l0 ^  l1                 // not used
        if ((left_rhs0 == not_right_rhs0 && left_rhs1 == not_right_rhs1) || 
            (left_rhs0 == not_right_rhs1 && left_rhs1 == not_right_rhs0)) {
            const unsigned rhs0 = left_rhs0, rhs1 = left_rhs1;
            if (have_same_variable(rhs0, rhs1))
                return false;
            if (rhs0ptr)
                *rhs0ptr = rhs0;
            if (rhs1ptr)
                *rhs1ptr = rhs1;
            return true;
        }
        return false;
    }

    bool is_ite(aiger *aiger, unsigned lit, unsigned *cond_lit_ptr,
                unsigned *then_lit_ptr, unsigned *else_lit_ptr) {
        aiger_and *and, *left, *right;
        unsigned left_rhs0, left_rhs1;
        unsigned right_rhs0, right_rhs1;
        unsigned not_left_rhs0, not_left_rhs1;
        unsigned not_right_rhs0, not_right_rhs1;
        unsigned cond_lit, then_lit, else_lit;
        
        and = aiger_is_and(aiger, lit);
        if (!and)
            return false;
        if (!aiger_sign(and->rhs0))
            return false;
        if (!aiger_sign(and->rhs1))
            return false;
        left = aiger_is_and(aiger, and->rhs0);
        if (!left)
            return false;
        right = aiger_is_and(aiger, and->rhs1);
        if (!right)
            return false;
        left_rhs0 = left->rhs0, left_rhs1 = left->rhs1;
        right_rhs0 = right->rhs0, right_rhs1 = right->rhs1;
        not_left_rhs0 = aiger_not(left_rhs0);
        not_left_rhs1 = aiger_not(left_rhs1);
        not_right_rhs0 = aiger_not(right_rhs0);
        not_right_rhs1 = aiger_not(right_rhs1);
        
        if (left_rhs0 == not_right_rhs0) {
            // (!l0 | !l1) & (!r0 | !r1)
            // (!l0 | !l1) & (l0 | !r1)
            // (l0 -> !l1) & (!l0 -> !r1)
            // l0 ? !l1 : !r1
            cond_lit = left_rhs0;
            then_lit = not_left_rhs1;
            else_lit = not_right_rhs1;
        } else if (left_rhs0 == not_right_rhs1) {
            // (!l0 | !l1) & (!r0 | !r1)
            // (!l0 | !l1) & (!r0 | l0)
            // (l0 -> !l1) & (!r0 <- !l0)
            // l0 ? !l1 : !r0
            cond_lit = left_rhs0;
            then_lit = not_left_rhs1;
            else_lit = not_right_rhs0;
        } else if (left_rhs1 == not_right_rhs0) {
            // (!l0 | !l1) & (!r0 | !r1)
            // (!l0 | !l1) & (l1 | !r1)
            // (!l0 <- l1) & (!l1 -> !r1)
            // l1 ? !l0 : !r1
            cond_lit = left_rhs1;
            then_lit = not_left_rhs0;
            else_lit = not_right_rhs1;
        } else if (left_rhs1 == not_right_rhs1) {
            // (!l0 | !l1) & (!r0 | !r1)
            // (!l0 | !l1) & (!r0 | l1)
            // (!l0 <- l1) & (!r0 <- !l1)
            // l1 ? !l0 : !r0
            cond_lit = left_rhs1;
            then_lit = not_left_rhs0;
            else_lit = not_right_rhs0;
        } else
            return false;
        
        if (aiger_is_constant(cond_lit))
            return false;
        if (aiger_is_constant(then_lit))
            return false;
        if (aiger_is_constant(else_lit))
            return false;
        if (!distinct_variables(cond_lit, then_lit, else_lit))
            return false;
        if (cond_lit_ptr)
            *cond_lit_ptr = cond_lit;
        if (then_lit_ptr)
            *then_lit_ptr = then_lit;
        if (else_lit_ptr)
            *else_lit_ptr = else_lit;
        return true;
    }

public:
    int convert(const std::vector<std::string> &args) {
        std::string input_name, output_name;
        unsigned i;
        
        for (i = 1; i < args.size(); i++) {
            if (args[i] == "-h") {
                std::cerr << "usage: aigtocnf [-h][-v][--no-coi][--no-pg][--no-xor][--no-ite] "
                             "[ <aig-file> [ <dimacs-file> ] ]" << std::endl;
                return 0;
            } else if (args[i] == "-m") {
                prtmap = true;
            } else if (args[i] == "-v") {
                verbose++;
            } else if (args[i] == "--no-coi") {
                nocoi = true;
            } else if (args[i] == "--no-pg") {
                nopg = true;
            } else if (args[i] == "--no-xor") {
                noxor = true;
            } else if (args[i] == "--no-ite") {
                noite = true;
            } else if (args[i].substr(0, 1) == "-") {
                die("invalid command line option '" + args[i] + "'");
            } else if (input_name.empty()) {
                input_name = args[i];
            } else if (output_name.empty()) {
                output_name = args[i];
            } else {
                die("more than two files specified");
            }
        }

        auto aiger = std::unique_ptr< ::aiger, decltype(&aiger_reset)>(aiger_init(), &aiger_reset);

        const char *error;
        if (!input_name.empty())
            error = aiger_open_and_read_from_file(aiger.get(), input_name.c_str());
        else
            error = aiger_read_from_file(aiger.get(), stdin);

        if (error)
            die(input_name.empty() ? std::string("<stdin>") + ": " + error : input_name + ": " + error);

        msg("read MILOA " + std::to_string(aiger->maxvar) + " " +
            std::to_string(aiger->num_inputs) + " " +
            std::to_string(aiger->num_latches) + " " +
            std::to_string(aiger->num_outputs) + " " +
            std::to_string(aiger->num_ands));

        if (aiger->num_latches)
            die("can not handle latches");
        if (aiger->num_bad)
            die("can not handle bad state properties (use 'aigmove')");
        if (aiger->num_constraints)
            die("can not handle environment constraints (use 'aigmove')");
        if (!aiger->num_outputs)
            die("no output");
        if (aiger->num_outputs > 1)
            die("more than one output");
        if (aiger->num_justice)
            wrn("ignoring justice properties");
        if (aiger->num_fairness)
            wrn("ignoring fairness constraints");

        std::ofstream outfile;
        std::ostream *output_stream = &std::cout;
        if (!output_name.empty()) {
            outfile.open(output_name);
            if (!outfile.is_open())
                die("failed to write '" + output_name + "'");
            output_stream = &outfile;
        }

        aiger_reencode(aiger.get());

        if (aiger->outputs[0].lit == 0) {
            msg("p cnf " + std::to_string(aiger->num_inputs) + " 1");
            *output_stream << "p cnf " << aiger->num_inputs << " 1\n0\n";
        } else if (aiger->outputs[0].lit == 1) {
            msg("p cnf " << std::to_string(aiger->num_inputs) << " 0");
            *output_stream << "p cnf " << aiger->num_inputs << " 0\n";
        } else {
            std::vector<unsigned> refs(2 * (aiger->maxvar + 1), 0);

            unsigned lit = aiger->outputs[0].lit;
            refs[lit]++;

            unsigned idx = aiger->num_ands;
            while (idx--) {
                unsigned not_lhs, not_rhs0, not_rhs1;
                unsigned cond_lit, then_lit, else_lit;
                unsigned not_cond, not_then, not_else;
                unsigned lhs, rhs0, rhs1;
                aiger_and *and;
                bool xor_result, ite_result;
                
                and = aiger->ands + idx;
                lhs = and->lhs;
                not_lhs = aiger_not(lhs);
                if (!refs[lhs] && !refs[not_lhs])
                    continue;
                    
                rhs0 = and->rhs0;
                rhs1 = and->rhs1;
                xor_result = !noxor && is_xor(aiger.get(), lhs, &rhs0, &rhs1);
                ite_result = !xor_result && !noite && is_ite(aiger.get(), lhs, &cond_lit, &then_lit, &else_lit);
                not_rhs0 = aiger_not(rhs0);
                not_rhs1 = aiger_not(rhs1);
                not_cond = aiger_not(cond_lit);
                not_then = aiger_not(then_lit);
                not_else = aiger_not(else_lit);
                
                if (ite_result) {
                    if (refs[lhs] || refs[not_lhs]) {
                        refs[cond_lit]++;
                        refs[not_cond]++;
                    }
                    if (refs[lhs]) {
                        refs[then_lit]++;
                        refs[else_lit]++;
                    }
                    if (refs[not_lhs]) {
                        refs[not_then]++;
                        refs[not_else]++;
                    }
                } else {
                    if (xor_result || refs[lhs]) {
                        refs[rhs0]++;
                        refs[rhs1]++;
                    }
                    if (xor_result || refs[not_lhs]) {
                        refs[not_rhs0]++;
                        refs[not_rhs1]++;
                    }
                }
            }

            if (nopg) {
                if (nocoi) {
                    for (lit = 2; lit <= 2 * aiger->maxvar + 1; lit++)
                        refs[lit] = std::numeric_limits<unsigned>::max();
                } else {
                    for (lit = 2; lit != 2 * aiger->maxvar; lit += 2) {
                        unsigned not_lit = lit + 1;
                        if (refs[lit] && !refs[not_lit])
                            refs[not_lit] = std::numeric_limits<unsigned>::max();
                        if (!refs[lit] && refs[not_lit])
                            refs[lit] = std::numeric_limits<unsigned>::max();
                    }
                }
            }

            std::vector<int> map(2 * (aiger->maxvar + 1), 0);
            int m = 0;
            int n = 1;
            if (refs[0] || refs[1]) {
                map[0] = -1;
                map[1] = 1;
                m++;
                n++;
            }
            for (lit = 2; lit <= 2 * aiger->maxvar; lit += 2) {
                unsigned not_lit = lit + 1;
                if (!refs[lit] && !refs[not_lit])
                    continue;
                map[lit] = ++m;
                map[not_lit] = -m;
                if (prtmap)
                    *output_stream << "c " << lit << " -> " << m << "\n";
                if (!aiger_is_and(aiger.get(), lit))
                    continue;
                if ((!noxor && is_xor(aiger.get(), lit, nullptr, nullptr)) ||
                    (!noite && is_ite(aiger.get(), lit, nullptr, nullptr, nullptr))) {
                    if (refs[lit])
                        n += 2;
                    if (refs[not_lit])
                        n += 2;
                } else {
                    if (refs[lit])
                        n += 2;
                    if (refs[not_lit])
                        n += 1;
                }
            }

            *output_stream << "p cnf " << m << " " << n << "\n";
            msg("p cnf " + std::to_string(m) + " " + std::to_string(n));

            if (refs[0] || refs[1])
                *output_stream << map[1] << " 0\n";

            for (idx = 0; idx < aiger->num_ands; idx++) {
                unsigned not_lhs, not_rhs0, not_rhs1;
                unsigned cond_lit, then_lit, else_lit;
                unsigned not_cond, not_then, not_else;
                unsigned lhs, rhs0, rhs1;
                aiger_and *and;
                bool xor_result, ite_result;
                
                and = aiger->ands + idx;
                lhs = and->lhs;
                rhs0 = and->rhs0;
                rhs1 = and->rhs1;
                xor_result = !noxor && is_xor(aiger.get(), lhs, &rhs0, &rhs1);
                ite_result = !xor_result && !noite && is_ite(aiger.get(), lhs, &cond_lit, &then_lit, &else_lit);
                not_lhs = aiger_not(lhs);
                not_rhs0 = aiger_not(rhs0);
                not_rhs1 = aiger_not(rhs1);
                not_cond = aiger_not(cond_lit);
                not_then = aiger_not(then_lit);
                not_else = aiger_not(else_lit);
                
                if (refs[lhs]) {
                    if (xor_result) {
                        *output_stream << map[not_lhs] << " " << map[rhs0] << " " << map[rhs1] << " 0\n";
                        *output_stream << map[not_lhs] << " " << map[not_rhs0] << " " << map[not_rhs1] << " 0\n";
                    } else if (ite_result) {
                        *output_stream << map[not_lhs] << " " << map[not_cond] << " " << map[then_lit] << " 0\n";
                        *output_stream << map[not_lhs] << " " << map[cond_lit] << " " << map[else_lit] << " 0\n";
                    } else {
                        *output_stream << map[not_lhs] << " " << map[rhs1] << " 0\n";
                        *output_stream << map[not_lhs] << " " << map[rhs0] << " 0\n";
                    }
                }
                if (refs[not_lhs]) {
                    if (xor_result) {
                        *output_stream << map[lhs] << " " << map[rhs0] << " " << map[not_rhs1] << " 0\n";
                        *output_stream << map[lhs] << " " << map[not_rhs0] << " " << map[rhs1] << " 0\n";
                    } else if (ite_result) {
                        *output_stream << map[lhs] << " " << map[not_cond] << " " << map[not_then] << " 0\n";
                        *output_stream << map[lhs] << " " << map[cond_lit] << " " << map[not_else] << " 0\n";
                    } else
                        *output_stream << map[lhs] << " " << map[not_rhs1] << " " << map[not_rhs0] << " 0\n";
                }
            }

            *output_stream << map[aiger->outputs[0].lit] << " 0\n";
        }

        return 0;
    }
};

int main(int argc, char **argv) {
    std::vector<std::string> args;
    for (int i = 0; i < argc; i++) {
        args.push_back(argv[i]);
    }
    
    AigToCnfConverter converter;
    return converter.convert(args);
}
