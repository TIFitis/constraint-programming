//========================================================================================================================================================
// Name        : CS18MTECH11023-incomplete-sat.cpp.cpp
// Author      : Akash Banerjee (CS18MTECH11023)
// Description : Incomplete-SAT Solver in C++, Ansi-style
//               There are 2 methods implemented:
//               1: Break-only-poly algorithm found at - https://www.uni-ulm.de/fileadmin/website_uni_ulm/iui.inst.190/Mitarbeiter/balint/SAT2012.pdf
//               2: WalkSat found at - http://www.cs.cornell.edu/~sabhar/chapters/IncompleteAlg-SAT-Handbook-prelim.pdf
//               Note: The final submission uses WalkSat without random restarts.
//========================================================================================================================================================

#include <iostream>
#include <vector>
#include <limits>
#include <random>
#include <time.h>
#include <cmath>
#include <bits/stdc++.h>

// Compile with '-DDEBUG' flag to enable debug print statements.
#ifdef DEBUG
#include <chrono>
#endif //DEBUG

std::default_random_engine rand_eng((unsigned long) time(0));

typedef std::vector<long> clause_t;
typedef std::vector<std::pair<clause_t, long>> sat_instance_t;
typedef std::vector<long> model_t;

static long no_of_variables;
static long no_of_clauses;
std::vector<long> vars_asgnd_by_unit_prop;

static double cb = 2.3;

#ifdef DEBUG
void print_sat_instance(const sat_instance_t &);
#endif //DEBUG

inline bool compare_scores(std::pair<double, long>, std::pair<double, long>);
inline long abs(long);
void initialize_sat_instance(sat_instance_t&);
void assign_literal(sat_instance_t&, long literal);
void assign_literal(sat_instance_t&, long literal,
                    std::vector<long>& new_unit_clauses);
void unit_clause_removal(sat_instance_t&, std::vector<long> &literals_assigned);
long verify_model(const sat_instance_t&, const model_t&,
                  clause_t &rand_unsat_clause);
inline model_t get_rand_model(const std::vector<long> &literals_assigned);
inline void print_model(const model_t&, long unsat);
long calc_break(const sat_instance_t&, const model_t&, long lit);
inline double break_only_poly(const sat_instance_t&, const model_t&, long lit);
model_t solve(sat_instance_t&, long);

#ifdef DEBUG
void print_sat_instance(const sat_instance_t &sat_instance) {
    for (auto a : sat_instance) {
        for (auto i : a.first) {
            std::cout << i << ' ';
        }
        std::cout << '\n';
    }
}
#endif //DEBUG

//Input :   Two scores.
//
//Output:   Return Score_1 < Score_2.
inline bool compare_scores(std::pair<double, long> n1,
                           std::pair<double, long> n2) {
    return n1.first < n2.first;
}

//Input :   Long.
//
//Output:   Absolute value of the long.
inline long abs(long a) {
    if (a < 0) return -a;
    return a;
}

//Input :   Reference to a sat_instance.
//
//Output:   Initialize the  provided   sat_instance
void initialize_sat_instance(sat_instance_t &sat_instance) {
    char a;
    std::cin >> a;
    while (a != 'p') {
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        std::cin >> a;
    }
    std::cin.ignore(5);
    std::cin >> no_of_variables;
    std::cin >> no_of_clauses;

    sat_instance.reserve(no_of_clauses);
    for (long i = 0; i < no_of_clauses; i++) {
        long literal;
        clause_t clause;
        std::cin.ignore(10, '\n');
        while (true) {
            std::cin >> literal;
            if (!std::cin.good()) {
                std::cin.clear();
                std::cin.ignore(std::numeric_limits<std::streamsize>::max(),
                                '\n');
                continue;
            }
            if (literal == 0) break;
            clause.push_back(literal);
        }
        sat_instance.push_back(std::make_pair(clause, i));
    }
}

//Input :   Sat instance and a literal.
//
//Output:   Does unit propagation on the sat instance,
//          for the input literal.
void assign_literal(sat_instance_t& sat_instance, long literal) {
    for (auto i = sat_instance.begin(); i < sat_instance.end(); i++) {
        bool flag = false;
        for (auto j = i->first.begin(); j < i->first.end(); j++) {
            if (*j == (-literal)) {
                *j = std::move(i->first.back());
                i->first.pop_back();
            }
            else if (*j == literal) {
                flag = true;
                break;
            }
        }
        if (flag) {
            *i = std::move(sat_instance.back());
            sat_instance.pop_back();
            i--;
        }
    }
}

//Input :   Reference  to a sat instance, and  a  literal.
//
//Output:   Modify the sat_instance to remove all clauses
//          where  that literal  is  present  and  remove
//          the negation of that literal from all clauses
//          and also return the number of clauses removed.
//          If any assignment causes  clause size to reduce
//          to 1 then add that clause to new_unit_clauses.
void assign_literal(sat_instance_t& sat_instance, long literal,
                    std::vector<long>& new_unit_clauses) {

    for (auto i = sat_instance.begin(); i < sat_instance.end(); i++) {
        bool flag = false;
        for (auto j = i->first.begin(); j < i->first.end(); j++) {
            if (*j == (-literal)) {

                *j = std::move(i->first.back());
                i->first.pop_back();

                if (i->first.size() == 1) {
                    new_unit_clauses.push_back(i->first.at(0));
                }

                break;
            }
            else if (*j == literal) {
                flag = true;
                break;
            }
        }
        if (flag) {
            *i = std::move(sat_instance.back());
            sat_instance.pop_back();
            i--;
        }
    }
}

//Input :   Sat instance.
//
//Output:   Modify the  sat_instance  by removing all unit  clauses from
//          it and add assigned literals to the literals_assigned vector.
//          Used to perform unit propagation on original sat instance.
void unit_clause_removal(sat_instance_t& sat_instance,
                         std::vector<long>& literals_assigned) {
    std::vector<long> clauses_to_be_removed;
    for (auto a : sat_instance) {
        if (a.first.size() == 1) {
            literals_assigned.push_back(a.first[0]);
            assign_literal(sat_instance, a.first[0], clauses_to_be_removed);
        }
    }
    while (!clauses_to_be_removed.empty()) {
        long literal = clauses_to_be_removed.back();
        clauses_to_be_removed.pop_back();
        literals_assigned.push_back(literal);
        assign_literal(sat_instance, literal, clauses_to_be_removed);
    }
    long i = 0;
    for (auto &a : sat_instance) {
        a.second = i;
        i++;
    }

    vars_asgnd_by_unit_prop.reserve(literals_assigned.size());
    for (auto a : literals_assigned) {
        vars_asgnd_by_unit_prop.push_back(abs(a));
    }
}

//Input :   Sat instance, model.
//
//Output:   Returns the no. of clauses that remain unsatisfied
//          using the current model, and also sets the input clause
//          to one of the random unsatisfied clauses if possible.
//          Returns 0 if model satisfies the given sat instance.
long verify_model(const sat_instance_t & sat_instance, const model_t &model,
                  clause_t &rand_unsat_clause) {
    auto dupl_instance = sat_instance;

    for (long i = 0; i < no_of_variables && !dupl_instance.empty(); i++) {
        if (std::find(vars_asgnd_by_unit_prop.begin(),
                      vars_asgnd_by_unit_prop.end(), i + 1)
                == vars_asgnd_by_unit_prop.end()) assign_literal(dupl_instance,
                                                                 model[i]);
    }

    if (dupl_instance.empty()) return 0;

    long random_unsat_clause_index = dupl_instance[rand_eng()
            % dupl_instance.size()].second;
    rand_unsat_clause = sat_instance[random_unsat_clause_index].first;
    return (long) dupl_instance.size();
}

//Input :   int vector of assigned literals
//
//Output:   Return a randomly generated model which
//          respects the already assigned literals
inline model_t get_rand_model(const std::vector<long> &literals_assigned) {
    model_t model(no_of_variables);
    long i = 1;
    for (auto &a : model) {
        auto rand = rand_eng() % 2;
        if (rand == 0)
            a = i;
        else
            a = -i;
        i++;
    }

    for (auto a : literals_assigned) {
        model[abs(a) - 1] = a;
    }

    return std::move(model);
}

//Input :   Model, and no. of unsat clauses using the model.
//
//Output:   Prints the no.of clauses satisfied and the model,
//          according to the syntax given in the problem.
inline void print_model(const model_t &model, long unsat) {
    static bool need_nl = false;
    if (!need_nl)
        need_nl = true;
    else
        std::cout << '\n';
    std::cout << no_of_clauses - unsat << "\nv ";
    for (auto a : model)
        std::cout << a << ' ';
    std::cout << '0';
    fflush(stdout);
}

//Input :   Sat instance, model, and a literal.
//
//Output:   Returns the break_score, i.e, the no of satisfied
//          clauses that would turn unsatisfied by flipping the
//          input literal in the given model.
long calc_break(const sat_instance_t &sat_instance, const model_t &model,
                long lit) {

    auto dupl_instance_1 = sat_instance;

    for (long i = 0; i < no_of_variables && !dupl_instance_1.empty(); i++) {
        if ((i == abs(lit) - 1)
                || (std::find(vars_asgnd_by_unit_prop.begin(),
                              vars_asgnd_by_unit_prop.end(), i + 1)
                        != vars_asgnd_by_unit_prop.end())) continue;
        assign_literal(dupl_instance_1, model[i]);
    }
    auto dupl_instance_2 = dupl_instance_1;

    assign_literal(dupl_instance_1, model[(abs(lit) - 1)]);
    assign_literal(dupl_instance_2, -model[(abs(lit) - 1)]);

    long break_score = 0;
    for (auto a : dupl_instance_2) {
        if (std::find(dupl_instance_1.begin(), dupl_instance_1.end(), a)
                == dupl_instance_1.end()) {
            break_score++;
        }
    }
    return break_score;
}

//Input :   Sat instance, model and a literal.
//
//Output:   Returns a score using the break_only
//          polynomial algorithm as described in the paper
//          mentioned in the description(Top of this file).
inline double break_only_poly(const sat_instance_t &sat_instance,
                              const model_t &model, long lit) {
    return pow((double) calc_break(sat_instance, model, lit), -cb);
}

//Input :   Input a sat instance, and an unsigned, specifying no. of
//          flips allowed before restarting, no. of variables by default.
//
//Output:   Uses a probabilistic incomplete SAT approach to find
//          a satisfying assignment for the input sat instance.
model_t solve(sat_instance_t &sat_instance, long max_flips = no_of_clauses) {
    long min_unsat = no_of_clauses;  //Stores the lowest no. of unsatisfied clauses currently found.
    std::vector<long> literals_assigned;
    unit_clause_removal(sat_instance, literals_assigned);
    while (true) {
        auto model = get_rand_model(literals_assigned);
        clause_t rand_unsat_clause;
        unsigned flip_count = 0;
        while (true) {
//            if (flip_count > max_flips) {
//                max_flips *= 2;
//                cb -= 0.1;
//                break;
//            }
            long cur_unsat = verify_model(sat_instance, model,
                                          rand_unsat_clause);

            if (cur_unsat < min_unsat) {
                flip_count = 0;
                min_unsat = cur_unsat;
                print_model(model, min_unsat);
                if (!min_unsat) return model;
            }
//            The following commented out code, uses polynomial-break only function to
//            caluclate score, to use this, the code must be uncommented and the code
//            from lines 350 - 397 must be commented.

//            std::vector<std::pair<double, long>> scores(
//                    rand_unsat_clause.size());
//            long i = 0;
//            for (auto a : rand_unsat_clause) {
//                scores[i].first = break_only_poly(sat_instance, model, a);
//                scores[i].second = a;
//                i++;
//            }
//            auto max_score = std::max_element(scores.begin(), scores.end());
//            long flip_var;
//            if (max_score->first == std::numeric_limits<double>::infinity()) {
//                flip_var = abs(max_score->second);
//            }
//            else {
//                std::uniform_real_distribution<double> unif(0,
//                                                            max_score->first);
//                double rnd = 0.0;
//                while (rnd == 0.0)
//                    rnd = unif(rand_eng);
//                i = 0;
//                while (rnd > scores[i].first)
//                    i++;
//                flip_var = abs(scores[i].second);
//            }

            std::vector<std::pair<long, long>> scores(rand_unsat_clause.size());
            long i = 0;
            for (auto a : rand_unsat_clause) {
                scores[i].first = calc_break(sat_instance, model, a);
                scores[i].second = a;
                if (scores[i].first == 0) break;
                i++;
            }
            auto min_score = std::min_element(scores.begin(), scores.end(),
                                              compare_scores);
            long flip_var;
            if (min_score->first == 0)
                flip_var = abs(min_score->second);
            else {
                auto rnd = rand_eng() % 2;          // p set as 1/2 for WalkSat.
                if (rnd == 0) {
                    auto rnd_element = rand_eng() % scores.size();
                    flip_var = abs(scores[rnd_element].second);
                }
                else {
                    flip_var = abs(min_score->second);
                }
            }

            model[flip_var - 1] = -model[flip_var - 1];
            flip_count++;
        }
    }
}

int main() {

#ifdef DEBUG
    auto start_time = std::chrono::high_resolution_clock::now();
#endif //DEBUG

    sat_instance_t sat_instance;
    initialize_sat_instance(sat_instance);

    auto model = solve(sat_instance);

#ifdef DEBUG
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast < std::chrono::milliseconds
    > (end_time - start_time);
    std::cout << "\nTime Taken: ";
    std::cout << duration.count() << std::endl;
#endif //DEBUG

    return 0;
}
