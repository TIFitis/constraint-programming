//============================================================================
// Name        : CS18MTECH11023-sat.cpp
// Author      : Akash Banerjee (cs18mtech11023@iith.ac.in)
// Description : DPLL Sat Solver in C++11, Ansi-style
//               Input  a  sat  instance  in  the  simplified  DIMACS  format
//               through stdin  and  output either UNSAT or SAT followed by a
//               satisfying  assignment on  the next line in  minisat2 format.
//============================================================================

#include <iostream>
#include <limits>
#include <vector>
#include <bits/stdc++.h>

typedef std::vector<int> clause_t;
typedef std::vector<clause_t> sat_instance_t;

static unsigned no_of_variables;
static unsigned no_of_clauses;

inline bool absolute_comparator(int i, int j);
inline unsigned max(unsigned i, unsigned j);
void print_sat_instance(const sat_instance_t& sat_instance);
void initialize_sat_instance(sat_instance_t& sat_instance);
inline bool has_empty_clause(const sat_instance_t& sat_instance);
inline int pick_literal(const sat_instance_t& sat_instance);
unsigned assign_literal(sat_instance_t& sat_instance, int literal);
unsigned assign_literal(sat_instance_t& sat_instance, int literal,
                        std::vector<int>& new_unit_clauses);
unsigned unit_clause_removal(sat_instance_t& sat_instance);
unsigned unit_clause_removal(sat_instance_t& sat_instance,
                             std::vector<int>& literals_assigned);
bool dpll(sat_instance_t& sat_instance,
          std::vector<int>& satisfying_assignment);

//  Comparator for output sorted on absolute value.
inline bool absolute_comparator(int i, int j) {
    return abs(i) < abs(j);
}

//  Returns max of two integers.
inline unsigned max(unsigned i, unsigned j) {
    return i > j ? i : j;
}

//Input :   A sat_instance.
//
//Output:   Print that sat_instance in CNF form.
//
//          ****ONLY USED FOR DEBUG PURPOSES****
void print_sat_instance(const sat_instance_t& sat_instance) {
    for (auto a : sat_instance) {
        for (auto i : a) {
            std::cout << i << ' ';
        }
        std::cout << '\n';
    }
}

//Input :   Reference to a sat_instance.
//
//Output:   Initialize the  provided   sat_instance
//          and also return the number of variables.
void initialize_sat_instance(sat_instance_t& sat_instance) {
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
    for (unsigned i = 0; i < no_of_clauses; i++) {
        int literal;
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
            if (literal == 0)
                break;
            clause.push_back(literal);
        }
        sat_instance.push_back(clause);
    }
}

//Input :   A sat_instance.
//
//Output:   Returns true if the sat_instance has
//          an empty clause and false  otherwise.
inline bool has_empty_clause(const sat_instance_t& sat_instance) {
    for (auto a : sat_instance) {
        if (a.empty())
            return true;
    }

    return false;
}

//Input :   A sat_nstance.
//
//Output:   Find the Most Occuring variable in the Minimum Sized clause.
int pick_literal(const sat_instance_t& sat_instance) {

    unsigned *variable_count = new unsigned[no_of_variables + 1];

    for (unsigned i = 0; i <= no_of_variables; i++)
        variable_count[i] = 0;

    sat_instance_t only_min_clauses;
    unsigned min_clause_size =
            static_cast<unsigned>(sat_instance.front().size());

    for (auto i : sat_instance) {
        if (i.size() < min_clause_size) {
            min_clause_size = static_cast<unsigned>(i.size());
            only_min_clauses.clear();
            only_min_clauses.push_back(i);
        } else if (i.size() == min_clause_size) {
            only_min_clauses.push_back(i);
        }
    }

    for (auto i : only_min_clauses)
        for (auto j : i)
            variable_count[abs(j)]++;

    unsigned max_occurrence = 0;
    unsigned max_occurring_variable = 0;
    for (unsigned i = 0; i <= no_of_variables; i++) {
        if (variable_count[i] > max_occurrence) {
            max_occurrence = variable_count[i];
            max_occurring_variable = i;
        }
    }

    return static_cast<int>(max_occurring_variable);

//    return sat_instance.front().front();

////    Try to combine MOMS with UnitPropagation for more accurate estimation.
////
//    unsigned max_unit_propagation = 0;
//    int max_unit_propagation_literal = 0;
//    for(int i = 0; i <= no_of_variables; i++){
//        if(literals[i] == max_occurrence){
//
//            sat_instance_t branch_assignment = sat_instance;
//            unsigned a = assign_literal(branch_assignment, i);
//            a += unit_clause_removal(branch_assignment);
//            if(has_empty_clause(branch_assignment)){
//                a = 0;
//            }
//
//            branch_assignment = sat_instance;
//            unsigned b = assign_literal(branch_assignment, -i);
//            b += unit_clause_removal(branch_assignment);
//            if(has_empty_clause(branch_assignment)){
//                b = 0;
//            }
//            if(max(a, b) > max_unit_propagation){
//                max_unit_propagation = max(a, b);
//                max_unit_propagation_literal = a>b?i:-i;
//            }
//        }
//    }
//    return max_unit_propagation_literal;
}

//Input :   Reference  to a sat instance, and  a  literal.
//
//Output:   Modify the sat_instance to remove all clauses
//          where  that literal  is  present  and  remove
//          the negation of that literal from all clauses
//          and also return the number of clauses removed.
unsigned assign_literal(sat_instance_t& sat_instance, int literal) {

    unsigned no_of_clauses_removed = 0;

    for (auto i = sat_instance.begin(); i < sat_instance.end(); i++) {
        bool flag = false;
        for (auto j = i->begin(); j < i->end(); j++) {
            if (*j == (-literal)) {
//                i->erase(j);
                *j = std::move(i->back());
                i->pop_back();
                break;
            } else if (*j == literal) {
                flag = true;
                break;
            }
        }
        if (flag) {
            no_of_clauses_removed++;
            *i = std::move(sat_instance.back());
            sat_instance.pop_back();
//            sat_instance.erase(i);
            i--;
        }
    }
    return no_of_clauses_removed;
}

//Overload  :   If any assignment causes  clause size to reduce
//              to one then add that clause to new_unit_clauses.
unsigned assign_literal(sat_instance_t& sat_instance, int literal,
                        std::vector<int>& new_unit_clauses) {

    unsigned no_of_clauses_removed = 0;

    for (auto i = sat_instance.begin(); i < sat_instance.end(); i++) {
        bool flag = false;
        for (auto j = i->begin(); j < i->end(); j++) {
            if (*j == (-literal)) {
//                i->erase(j);
                *j = std::move(i->back());
                i->pop_back();

                if (i->size() == 1) {
                    new_unit_clauses.push_back(i->at(0));
                }
                break;
            } else if (*j == literal) {
                flag = true;
                break;
            }
        }
        if (flag) {
            no_of_clauses_removed++;
//            sat_instance.erase(i);
            *i = std::move(sat_instance.back());
            sat_instance.pop_back();
            i--;
        }
    }
    return no_of_clauses_removed;
}

//Input :   Reference to a sat_instance and reference to a vector<int>.
//
//Output:   Modify the  sat_instance  by removing all unit  clauses from
//          it and add assigned literals to the literals_assigned vector.
unsigned unit_clause_removal(sat_instance_t& sat_instance,
                             std::vector<int>& literals_assigned) {
    std::vector<int> clauses_to_be_removed;
    unsigned no_of_clauses_removed = 0;
    for (auto a : sat_instance) {
        if (a.size() == 1) {
            literals_assigned.push_back(a[0]);
            no_of_clauses_removed += assign_literal(sat_instance, a[0],
                                                    clauses_to_be_removed);
        }
    }
    while (!clauses_to_be_removed.empty()) {
        int literal = clauses_to_be_removed.back();
        clauses_to_be_removed.pop_back();
        literals_assigned.push_back(literal);
        no_of_clauses_removed += assign_literal(sat_instance, literal,
                                                clauses_to_be_removed);
    }
    return no_of_clauses_removed;
}

//Overload  :   Does not place assigned literals on the output vector.
unsigned unit_clause_removal(sat_instance_t& sat_instance) {
    std::vector<int> clauses_to_be_removed;
    unsigned no_of_clauses_removed = 0;
    for (auto a : sat_instance) {
        if (a.size() == 1) {
            no_of_clauses_removed += assign_literal(sat_instance, a[0],
                                                    clauses_to_be_removed);
        }
    }
    while (!clauses_to_be_removed.empty()) {
        int literal = clauses_to_be_removed.back();
        clauses_to_be_removed.pop_back();
        no_of_clauses_removed += assign_literal(sat_instance, literal,
                                                clauses_to_be_removed);
    }
    return no_of_clauses_removed;
}

//Input :   A sat_instance and a reference to a vector<int>.
//
//Output:   Use  the  DPLL  algorithm  to   find  a  satisfiable
//          assignment and return TRUE along with the assignment
//          placed on the input vector<int>. Else  return  FALSE
//          if a satisfying does not exist.
//
//Note  :   sat_instance provided as input  may  get  modified
//          but is not an output and is taken as reference  to
//          avoid   copying   and  improve   performance  only.
bool dpll(sat_instance_t& sat_instance,
          std::vector<int>& satisfying_assignment) {
    std::vector<int> literals_assigned_by_unit_propagation;
    unit_clause_removal(sat_instance, literals_assigned_by_unit_propagation);

    if (sat_instance.empty()) {
        satisfying_assignment.insert(
                satisfying_assignment.end(),
                literals_assigned_by_unit_propagation.begin(),
                literals_assigned_by_unit_propagation.end());
        return true;
    }

    if (has_empty_clause(sat_instance)) {
        return false;
    }

    int literal = pick_literal(sat_instance);
    if (!literal)
        return false;

    sat_instance_t branch_assignment = sat_instance;
    assign_literal(branch_assignment, literal);
    if (dpll(branch_assignment, satisfying_assignment)) {
        satisfying_assignment.push_back(literal);
        satisfying_assignment.insert(
                satisfying_assignment.end(),
                literals_assigned_by_unit_propagation.begin(),
                literals_assigned_by_unit_propagation.end());
        return true;
    }

    branch_assignment = sat_instance;
    assign_literal(branch_assignment, -literal);
    if (dpll(branch_assignment, satisfying_assignment)) {
        satisfying_assignment.push_back(-literal);
        satisfying_assignment.insert(
                satisfying_assignment.end(),
                literals_assigned_by_unit_propagation.begin(),
                literals_assigned_by_unit_propagation.end());
        return true;
    }

    return false;
}

int main() {
    auto start_time = std::chrono::high_resolution_clock::now();

    sat_instance_t sat_instance;
    initialize_sat_instance(sat_instance);

    std::vector<int> result;
    if (dpll(sat_instance, result)) {
        std::cout << "SAT\n";
        sort(result.begin(), result.end(), absolute_comparator);

        unsigned track_unused_variables = 1;
        int track_duplicate_print = 0;

        for (auto a : result) {
            while (static_cast<unsigned>(abs(a)) > track_unused_variables
                    && track_unused_variables <= no_of_variables) {
//                std::cout << track_unused_variables << ' ';
                track_unused_variables++;
            }
            if (static_cast<unsigned>(abs(a)) <= no_of_variables
                    && a != track_duplicate_print) {
                std::cout << a << ' ';
                track_duplicate_print = a;
            }
            track_unused_variables++;
        }

        std::cout << 0;
    } else {
        std::cout << "UNSAT";
    }

    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast<std::chrono::milliseconds>(
            end_time - start_time);
    std::cout << "\nTime Taken: ";
    std::cout << duration.count() << std::endl;
    return 0;
}

//TIFitis :)

