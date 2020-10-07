//============================================================================
// Name        : CS18MTECH11023-maxsat.cpp
// Author      : Akash Banerjee (CS18MTECH11023)
// Description : LUS MaxSAT using Totalizer Encoding in C++, Ansi-style
//============================================================================

#include <iostream>
#include <vector>
#include <limits>

// Compile with '-DDEBUG' flag to enable debug print statements.
#ifdef DEBUG
#include <chrono>
#endif //DEBUG

#include <core/Solver.h>

typedef std::vector<int> clause_t;
typedef std::vector<clause_t> sat_instance_t;

static unsigned no_of_variables;
static unsigned no_of_clauses;

static unsigned relax_variables_counter;

static unsigned totalizer_output_variables_begin;
static unsigned totalizer_variables_counter;

static unsigned total_no_of_variables;
static unsigned total_no_of_clauses;

#ifdef DEBUG
void print_sat_instance(const sat_instance_t &);
#endif //DEBUG

void initialize_sat_instance(sat_instance_t&);
void initialize_minisat_instance(sat_instance_t &, Minisat::Solver &);
unsigned apply_totalizer_encoding(sat_instance_t &, unsigned, unsigned);

#ifdef DEBUG
void print_sat_instance(const sat_instance_t &sat_instance) {
    for (auto a : sat_instance) {
        for (auto i : a) {
            std::cout << i << ' ';
        }
        std::cout << '\n';
    }
}
#endif //DEBUG

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

    totalizer_variables_counter = no_of_variables;
    total_no_of_variables = no_of_variables;
    total_no_of_clauses = no_of_clauses;

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
            if (literal == 0) break;
            clause.push_back(literal);
        }
        sat_instance.push_back(clause);
    }
}

//Input :   Reference to a sat_instance and a
//          minisat solver instance.
//
//Output:   Initialize the  minisat solver instance
//          using the sat_instance.
inline void initialize_minisat_instance(sat_instance_t &sat_instance,
                                        Minisat::Solver &ms_solver) {
    ms_solver.newVar();
    for (unsigned i = 1; i <= total_no_of_variables; i++) {
        ms_solver.newVar();
    }
    for (clause_t clause : sat_instance) {
        Minisat::vec < Minisat::Lit > temp_clause;
        for (int lit : clause) {
            temp_clause.push(Minisat::mkLit(abs(lit), ((lit) < 0)));
        }
        ms_solver.addClause(temp_clause);
    }
}

//Input :   Reference to a sat_instance.
//
//Output:   Add Relax variables to all the clauses,
//          and also add the totalizer encoding
//          cardinality constraint clauses to the sat_instance.
unsigned apply_totalizer_encoding(
        sat_instance_t &sat_instance, unsigned lb = no_of_variables + 1,
        unsigned ub = no_of_variables + no_of_clauses) {
    if ((ub - lb) == 0) {
        sat_instance[relax_variables_counter].push_back(
                ++totalizer_variables_counter);
        relax_variables_counter++;
        total_no_of_variables++;
        return totalizer_variables_counter - 1;
    }

    unsigned mid = (ub + lb) / 2;
    unsigned begin_l = apply_totalizer_encoding(sat_instance, lb, mid);
    unsigned begin_r = apply_totalizer_encoding(sat_instance, mid + 1, ub);

    unsigned front = totalizer_variables_counter;
    unsigned length = ub - lb + 1;
    totalizer_variables_counter += length;
    total_no_of_variables += length;

    for (unsigned i = 0; i <= mid - lb + 1; i++) {
        for (unsigned j = 0; j <= ub - mid; j++) {
            if (i == 0 && j == 0) continue;
            clause_t clause;
            if (j == 0) {
                clause.push_back(-(int) (begin_l + i));
                clause.push_back(front + i + j);
            }
            else
                if (i == 0) {
                    clause.push_back(-(int) (begin_r + j));
                    clause.push_back(front + i + j);
                }
                else {
                    clause.push_back(-(int) (begin_l + i));
                    clause.push_back(-(int) (begin_r + j));
                    clause.push_back((int) (front + i + j));
                }
            sat_instance.push_back(clause);
            total_no_of_clauses++;
        }
    }
    return front;

}

int main() {

#ifdef DEBUG
    auto start_time = std::chrono::high_resolution_clock::now();
#endif //DEBUG

    sat_instance_t sat_instance;
    initialize_sat_instance(sat_instance);          //Parse the input

    totalizer_output_variables_begin = apply_totalizer_encoding(sat_instance)
            + 1;                                   //Apply totalizer encoding on the input.
#ifdef DEBUG
    std::cout << "Vars = " << no_of_variables << " Clauses = " << no_of_clauses
    << " Final Vars = " << total_no_of_variables
    << " Final Clauses = " << total_no_of_clauses
    << " Totalizer Begin = " << totalizer_output_variables_begin
    << std::endl;
#endif //DEBUG

    Minisat::Solver ms_solver;
    initialize_minisat_instance(sat_instance, ms_solver);   //Initialize the minisat solver instance.
    sat_instance.clear();

    Minisat::vec < Minisat::Lit > assumps;                  //Start by assuming all the totalizer output variables are negated
    unsigned no_of_relaxed_clauses = 0;
    for (unsigned i = total_no_of_variables;
            i >= totalizer_output_variables_begin; i--) {
        assumps.push(Minisat::mkLit(i, true));
    }
    while (!ms_solver.solve(assumps)) {                     //Every iteration remove one of the assumptions in ascending order
        assumps.pop();                                      //until the the formula is satisfiable.
        no_of_relaxed_clauses++;
    }

    std::cout << no_of_clauses - no_of_relaxed_clauses << std::endl;    //Print output.
    Minisat::lbool l_t((uint8_t) 0);
    for (unsigned i = 1; i <= no_of_variables; i++) {
        if (ms_solver.model[i] == l_t) {
            std::cout << i << ' ';
        }
        else
            std::cout << -(int) i << ' ';
    }
    std::cout << 0;

#ifdef DEBUG
    auto end_time = std::chrono::high_resolution_clock::now();
    auto duration = std::chrono::duration_cast < std::chrono::milliseconds
    > (end_time - start_time);
    std::cout << "\nTime Taken: ";
    std::cout << duration.count() << std::endl;
#endif //DEBUG

    return 0;
}
