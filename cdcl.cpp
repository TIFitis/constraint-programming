//============================================================================
// Name        : cs18mtech11023-sat.cpp
// Author      : Akash Banerjee (CS18MTECH11023@iith.ac.in)
// Description : DPLL Sat Solver in C++11, Ansi-style
//               Input  a  sat  instance  in  the  simplified  DIMACS  format
//               through stdin  and  output either UNSAT or SAT followed by a
//               satisfying  assignment on  the next line in  minisat2 format.
//============================================================================

#include <iostream>
#include <limits>
#include <vector>
#include <bits/stdc++.h>

static int* variable_assignments;
static int* variable_decision_level;
static double* variable_priority;

static double decay_factor = 0.5;

static unsigned no_of_variables;
static unsigned no_of_clauses;

static unsigned random_restart_conflicts;
static unsigned random_restart_threshold = 500;

class clause_t {
    std::unique_ptr<std::vector<int>> my_clause;
    std::vector<int>::iterator wl1;
    std::vector<int>::iterator wl2;

 public:
    clause_t()
            : my_clause { new std::vector<int>(0) } {
    }

    int& operator[](const unsigned index) {
        return (*my_clause)[index];
    }

    int is_unit() {
        int unassigned_count = 0, unassigned_literal = 0;
        for (auto a : *my_clause) {
            if (variable_assignments[abs(a)] == 0) {
//                std::cout << "in 1 checking assignment of : " << abs(a) << '\n';
                unassigned_count++;
                unassigned_literal = a;
            } else if (variable_assignments[abs(a)] == a) {
//                std::cout << "in 3 checking assignment of : " << abs(a)
//                          << " and comparing with" << a << '\n';
                return 0;
            }
            if (unassigned_count > 1)
                return 0;
        }
        if (unassigned_count == 1)
            return unassigned_literal;
        return 0;
    }

    bool is_unsatisfiable() {
        for (auto a : *my_clause) {
            if (variable_assignments[abs(a)] == a
                    || variable_assignments[abs(a)] == 0) {
                return false;
            }
        }
        return true;
    }

    void push_back(const int literal) {
        my_clause->push_back(literal);
    }

    std::vector<int>::iterator erase(std::vector<int>::iterator it) {
        return my_clause->erase(it);
    }

    std::vector<int>::iterator erase(std::vector<int>::iterator it1,
                                     std::vector<int>::iterator it2) {
        return my_clause->erase(it1, it2);
    }

    std::vector<int>::iterator begin() {
        return my_clause->begin();
    }

    std::vector<int>::iterator end() {
        return my_clause->end();
    }

    std::vector<int>::iterator watch_lit_1() {
        return wl1;
    }

    std::vector<int>::iterator watch_lit_2() {
        return wl2;
    }

    std::vector<int>::iterator set_watch_lit_1() {
        std::vector<int>::iterator temp = my_clause->end();
        for (std::vector<int>::iterator i = my_clause->begin();
                i < my_clause->end(); i++) {
//            std::cout << "atleast entered ... \n";
            if (variable_assignments[abs(*i)] == 0 && wl2 != i) {
                temp = i;
            }
//            std::cout << "yolo --- " << *i << '\n';
            if (variable_assignments[abs(*i)] == *i) {
                wl1 = i;
                return wl1;
            }
//            std::cout << "here now\n";
        }
        if (temp != my_clause->end())
            wl1 = temp;
        return wl1;
    }

    std::vector<int>::iterator set_watch_lit_2() {
        std::vector<int>::iterator temp = my_clause->end();
        for (std::vector<int>::iterator i = my_clause->end() - 1;
                i >= my_clause->begin(); i--) {
            if (variable_assignments[abs(*i)] == 0 && wl1 != i) {
                temp = i;
            }
            if (variable_assignments[abs(*i)] == *i) {
                wl2 = i;
                return wl2;
            }
        }
        if (temp != my_clause->end())
            wl2 = temp;
        return wl2;
    }

    void set_watch_lit_1(std::vector<int>::iterator it) {
        wl1 = it;
    }

    void set_watch_lit_2(std::vector<int>::iterator it) {
        wl2 = it;
    }

};

static std::shared_ptr<clause_t> null_clause;
typedef std::list<std::shared_ptr<clause_t>> sat_instance_t;
static sat_instance_t sat_instance;
//std::unique_ptr<std::vector<std::shared_ptr<clause_t>>> variables;
static std::set<std::shared_ptr<clause_t>> *variables;
static std::vector<std::shared_ptr<clause_t>> variable_antecedent;

static unsigned no_of_variables_assigned;

inline bool absolute_comparator(int i, int j) {
    return abs(i) < abs(j);
}

void print_status() {
//    for (auto &a : sat_instance) {
//        for (auto i : *a) {
//            std::cout << i << ' ';
//        }
//        std::cout << '\n';
//        std::cout << "watch 1 : " << *(*a).watch_lit_1() << '\n';
//        std::cout << "watch 2 : " << *(*a).watch_lit_2() << '\n';
//        std::cout << "Unit Status : " << (*a).is_unit() << '\n';
//    }
//
//    std::cout << "Printing Variables:\n\n";
//    for (unsigned i = 1; i <= no_of_variables; i++) {
//        for (auto& a : variables[i]) {
//            std::cout << i << "in clause: ";
//            for (auto b : *a)
//                std::cout << b << ' ';
//            std::cout << '\n';
//        }
//        std::cout << '\n';
//    }

    std::cout << "Printing Variable antecedents:\n\n";
    for (unsigned i = 1; i <= no_of_variables; i++) {
        std::cout << i << " Antecedent clause: ";
        if (variable_antecedent[i] != null_clause)
            for (auto b : *variable_antecedent[i])
                std::cout << b << ' ';
        std::cout << '\n';
    }

    std::cout << "Printing Variable Assignments:\n\n";
    for (unsigned i = 1; i <= no_of_variables; i++) {
        std::cout << variable_assignments[i] << ' '
                  << variable_decision_level[i] << '\n';
    }
    std::cout << '\n';
}

void initialize_sat_instance() {
    char a;
    std::cin >> a;
    while (a != 'p') {
        std::cin.ignore(std::numeric_limits<std::streamsize>::max(), '\n');
        std::cin >> a;
    }

    std::cin.ignore(5);
    std::cin >> no_of_variables;
    std::cin >> no_of_clauses;
    variables = new std::set<std::shared_ptr<clause_t>>[no_of_variables + 1];
    variable_antecedent = std::vector<std::shared_ptr<clause_t>>(
            no_of_variables + 1);
    variable_assignments = (int*) calloc((no_of_variables + 1), sizeof(int));
    variable_decision_level = (int*) calloc((no_of_variables + 1), sizeof(int));
    variable_priority = (double*) calloc(((no_of_variables << 1) + 2),
                                         sizeof(double));

    for (unsigned i = 1; i <= no_of_variables; i++) {
        variable_decision_level[i] = -1;
        variable_antecedent[i] = null_clause;
    }

    for (unsigned i = 0; i < no_of_clauses; i++) {
        int literal;
        std::shared_ptr<clause_t> clause { new clause_t };
        std::cin.ignore(10, '\n');
        while (true) {
            std::cin >> literal;
            if (!std::cin.good()) {
                std::cin.clear();
                std::cin.ignore(std::numeric_limits<std::streamsize>::max(),
                                '\n');
                continue;
            }
            if (literal == 0)
                break;
            clause->push_back(literal);
        }
        clause->set_watch_lit_1(clause->begin());
        clause->set_watch_lit_2(clause->end() - 1);
        variables[abs(*(clause->watch_lit_1()))].insert(clause);
        variables[abs(*(clause->watch_lit_2()))].insert(clause);
        sat_instance.push_back(clause);
    }
}

bool assign_literal(int literal, std::vector<int>& unit_literals,
                    std::vector<std::shared_ptr<clause_t>>& antecedants,
                    std::shared_ptr<clause_t>& unsat_clause) {
    variable_assignments[abs(literal)] = literal;
    no_of_variables_assigned++;
    int flag;
//    std::cout << "Set Variable assignment for " << literal << '\n';
    for (auto i = variables[abs(literal)].begin();
            i != variables[abs(literal)].end();) {
        flag = 0;
//        std::cout << "Size = " << variables[abs(literal)].size() << '\n';
//        std::cout << "Entered Loop\n";
        if (abs(*((*i)->watch_lit_1())) == abs(literal)) {
//            std::cout << "Attempting fix of watch literal 1  = "
//                      << *((*i)->watch_lit_1()) << '\n';
            (*i)->set_watch_lit_1();
            if (abs(*((*i)->watch_lit_1())) != abs(literal)) {
                flag = 1;
                variables[abs(*((*i)->watch_lit_1()))].insert(*i);
            }
        } else if (abs(*((*i)->watch_lit_2())) == abs(literal)) {
//            std::cout << "Attempting fix of watch literal 2  = "
//                      << *((*i)->watch_lit_2()) << '\n';
            (*i)->set_watch_lit_2();
            if (abs(*((*i)->watch_lit_2())) != abs(literal)) {
                flag = 1;
                variables[abs(*((*i)->watch_lit_2()))].insert(*i);
            }
        } else {
//            std::cout << abs(*((*i)->watch_lit_1())) << "   "
//                      << abs(*((*i)->watch_lit_2())) << "   " << abs(literal);
            std::cout << "\n\n!!!Fatal Warning!!!\n\n";
        }
//        std::cout << "Checking for unsatisfiability\n";
        if ((*i)->is_unsatisfiable()) {
            unsat_clause = *i;
            return false;
        }

//        std::cout << "Checking for unit clause\n";
        int a = (*i)->is_unit();
        if (a) {
//            std::cout << "Clause is unit so Pushing back " << a << '\n';
            unit_literals.push_back(a);
            antecedants.push_back(*i);
        }
        if (flag) {
//            std::cout << abs(*((*i)->watch_lit_1())) << "   "
//                      << abs(*((*i)->watch_lit_2())) << "   " << abs(literal);
//            std::cout << "Removed reference from variable\n";
            variables[abs(literal)].erase(i++);
        } else
            ++i;
//        i--;
    }
    return true;
}

bool unit_propagate(int decision_level,
                    std::shared_ptr<clause_t>& unsat_clause) {
    std::vector<int> unit_literals(0);
    std::vector<std::shared_ptr<clause_t>> antecedants;
    for (auto &a : sat_instance) {
        if ((*a).is_unsatisfiable()) {
            unsat_clause = a;
            return false;
        }
        int unit_literal = (*a).is_unit();
        if (unit_literal) {
            if (decision_level > 0) {
//                std::cout << "set variable antecedent for " << unit_literal
//                          << '\n';
                variable_antecedent[abs(unit_literal)] = a;
            }
            variable_decision_level[abs(unit_literal)] = decision_level;
//            std::cout << "\n\n\nAttempting to remove in 1: " << unit_literal
//                      << '\n';
            if (!assign_literal(unit_literal, unit_literals, antecedants,
                                unsat_clause))
                return false;
        }
    }
    while (!unit_literals.empty()) {
        int unit_literal = unit_literals.back();
        unit_literals.pop_back();

        if (decision_level > 0) {
//            std::cout << "set variable antecedent for " << unit_literal << '\n';
            variable_antecedent[abs(unit_literal)] = antecedants.back();
        }
        variable_decision_level[abs(unit_literal)] = decision_level;
        antecedants.pop_back();
//        std::cout << "\n\n\nAttempting to remove in 2: " << unit_literal
//                  << '\n';
        if (!assign_literal(unit_literal, unit_literals, antecedants,
                            unsat_clause))
            return false;
    }
    return true;
}

bool all_variables_assigned() {
    for (unsigned i = 1; i <= no_of_variables; i++) {
        if (variable_assignments[i] == 0) {
            return false;
        }
    }
    return true;
//    return no_of_variables_assigned == no_of_variables ? true : false;
}

int pick_literal() {
    int literal = no_of_variables;
    for (int i = 0; i < (int) (no_of_variables << 1) + 1; i++) {
        variable_priority[i] *= decay_factor;
//        std::cout << i-(int)no_of_variables << ' ' << variable_priority[i] << '\n';
    }
//    std::cout << '\n';
    for (int i = 0; i < (int) (no_of_variables << 1) + 1; i++) {
//        std::cout << i << '\t' << abs(i - (int) no_of_variables) << '\t'
//                  << variable_priority[i] << '\t'
//                  << variable_assignments[abs(i - (int) no_of_variables)]
//                  << '\n';
        if (variable_priority[i] >= variable_priority[literal]
                && variable_assignments[abs(i - (int) no_of_variables)] == 0) {
            literal = i;
        }
    }
//    std::cout << "returning " << literal - (int) no_of_variables << '\n';
    return literal - (int) no_of_variables;
}

bool resolution(std::shared_ptr<clause_t> clause1,
                std::shared_ptr<clause_t> clause2, int resolution_literal) {
//    std::cout << "Resolution literal : " << resolution_literal << '\n';
//    std::cout << "performing resolution for clauses: \n";
//    std::cout << "clause 1: ";
//    for (auto a : *clause1) {
//        std::cout << a << ' ';
//    }
//    std::cout << '\n';
//    std::cout << "clause 2: ";
//    for (auto a : *clause2) {
//        std::cout << a << ' ';
//    }
//    std::cout << '\n';
    clause1->erase(
            std::find(clause1->begin(), clause1->end(), resolution_literal));
    for (auto a : *clause2) {
        if (a != -resolution_literal
                && std::find(clause1->begin(), clause1->end(), a)
                        == clause1->end()) {
            clause1->push_back(a);
        }
    }
//    std::cout << "After resolution clause 1: ";
//    for (auto a : *clause1) {
//        std::cout << a << ' ';
//    }
//    std::cout << '\n';
    return false;
}

bool uip_clause(int decision_level, std::shared_ptr<clause_t> clause) {
    unsigned current_level__literals_count = 0;
    for (auto a : *clause) {
        if (variable_decision_level[abs(a)] == decision_level) {
            current_level__literals_count++;
            if (current_level__literals_count > 1)
                return false;
        }
    }
    if (current_level__literals_count == 1)
        return true;
    return false;
}

int conflict_analysis(int decision_level,
                      std::shared_ptr<clause_t> unsat_clause) {
    random_restart_conflicts++;
    std::shared_ptr<clause_t> learnt_clause { new clause_t };

    for (auto a : *unsat_clause) {
        learnt_clause->push_back(a);
    }
    std::set<int> resolved_variables;
    int flag = 1;
    while (flag) {
        flag = 0;
        for (auto a = learnt_clause->begin(); a < learnt_clause->end(); a++) {
            if (variable_antecedent[abs(*a)] != null_clause
                    && (resolved_variables.find(*a) == resolved_variables.end())) {
                flag = 1;
                resolved_variables.insert(*a);
                resolution(learnt_clause, variable_antecedent[abs(*a)], *a);
                if (uip_clause(decision_level, learnt_clause)) {
                    flag = 0;
                    break;
                }
                a = learnt_clause->begin();
            }
        }
    }
    int backtrack_level = 0;
    for (auto a : *learnt_clause) {
        variable_priority[a + no_of_variables]++;
        if (variable_decision_level[abs(a)] > backtrack_level
                && variable_decision_level[abs(a)] < decision_level)
            backtrack_level = variable_decision_level[abs(a)];
    }
    learnt_clause->set_watch_lit_1(learnt_clause->begin());
    learnt_clause->set_watch_lit_2(learnt_clause->end() - 1);
    variables[abs(*(learnt_clause->watch_lit_1()))].insert(learnt_clause);
    variables[abs(*(learnt_clause->watch_lit_2()))].insert(learnt_clause);
    sat_instance.push_back(learnt_clause);
//    if(backtrack_level > 0)
//        return backtrack_level-1;
    return backtrack_level;
}

void backtrack(int backtrack_level) {
    for (unsigned i = 1; i <= no_of_variables; i++) {
        if (variable_decision_level[i] > backtrack_level) {
            variable_assignments[i] = 0;
            no_of_variables_assigned--;
            variable_decision_level[i] = -1;
            variable_antecedent[i] = null_clause;
        }
    }
}

bool cdcl() {
    int decision_level = 0;
    std::shared_ptr<clause_t> unsat_clause;
    if (!unit_propagate(decision_level, unsat_clause)) {
        return false;
    }
    int flag = 1;
    while (!all_variables_assigned()) {
        if (flag) {
            int literal = pick_literal();
//            std::cout
//                    << "\n\n000000000000000000000000000000000000000000000000000000\n\nPicked Literal : "
//                    << literal << '\n';
            decision_level++;
            std::vector<std::shared_ptr<clause_t>> dummy_antecedants;
            std::vector<int> dummy_unit_literals;
            variable_decision_level[abs(literal)] = decision_level;
            if (!assign_literal(literal, dummy_unit_literals, dummy_antecedants,
                                unsat_clause)) {
//                std::cout
//                        << "!!!Decision assignment caused Conflict!!!\nEither unit_propagation or assign_literal is broken!\n\n";
            }
//            std::cout
//                    << "\n\n\n\n\nAssignment completed now unit propagating!!!!\n\n";
        }
        flag = 1;
        if (!unit_propagate(decision_level, unsat_clause)) {
            flag = 0;
//            std::cout
//                    << "===============\n\n===============\n\nUnit Propagation reproted conflict!\n\n";
            int backtrack_level = conflict_analysis(decision_level,
                                                    unsat_clause);
            if (backtrack_level < 0) {
//                std::cout
//                        << "+++++++++++++++++++++++++++++++\n\nBacktrack level < 0\nReturning UNSAT!!\n+++++++++++++++++++++++++++++\n";
                return false;
            }
//            std::cout << "Backtracking to " << backtrack_level << '\n';
//            std::cout << "\n\nPrinting Status! Before back track\n";
//            std::cout
//                    << "\n-------------------------------------------------------------------------------------------------\n";
//            print_status();
//            std::cout
//                    << "\n-------------------------------------------------------------------------------------------------\n\n";
            backtrack(backtrack_level);
            decision_level = backtrack_level;
            if(random_restart_conflicts > random_restart_threshold){
//                std::cout << "restarted!\n";
                random_restart_conflicts = 0;
//                std::cout << "restarted!" << random_restart_conflicts << '\n';
                backtrack_level = 0;
                backtrack(0);
            }
//            std::cout << "\n\nAfter back trackPrinting Status!\n";
//            std::cout
//                    << "\n-------------------------------------------------------------------------------------------------\n";
//            print_status();
//            std::cout
//                    << "\n-------------------------------------------------------------------------------------------------\n\n";
        }
    }
    return true;
}

int main() {
    auto start_time = std::chrono::high_resolution_clock::now();
    initialize_sat_instance();
//    print_status();
    if (cdcl()) {
        std::cout << "SAT\n";
        for (unsigned i = 1; i <= no_of_variables; i++)
            std::cout << variable_assignments[i] << ' ';
        std::cout << '0';
    } else
        std::cout << "UNSAT";

//    std::cout << "\n\n";
//    print_status();
    delete[] variables;
    free(variable_assignments);
    free(variable_decision_level);
    free(variable_priority);

    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(
            end_time - start_time);
    std::cout << "\nTime Taken: ";
    std::cout << duration.count() << std::endl;
    return 0;
}
