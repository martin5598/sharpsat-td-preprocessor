
#include "preprocessor/instance.hpp"
#include "preprocessor/preprocessor.hpp"
#include "preprocessor/treewidth.hpp"



#include <iostream>

#include <vector>
#include <limits>

#include <string>

#include <sys/time.h>
#include <sys/resource.h>
#include <gmpxx.h>
#include <limits>
#include "mpfr/mpreal.h"

#include <random>

using namespace std;


void PrintSat(bool sat) {
  if (sat) {
    cout<<"s SATISFIABLE"<<endl;
  } else {
    cout<<"s UNSATISFIABLE"<<endl;
  }
}

void PrintType(const sspp::Instance& ins) {
  if (ins.weighted) {
    cout<<"c s type wmc"<<endl;
  } else {
    cout<<"c s type mc"<<endl;
  }
}

mpfr::mpreal Log10(const mpz_class& num) {
  assert(num >= 0);
  if (num == 0) {
    return -std::numeric_limits<double>::infinity();
  }
  mpfr::mpreal num1(num.get_mpz_t());
  return mpfr::log10(num1);
}

void PrintLog10(const mpz_class& num) {
  cout<<"c s log10-estimate "<<Log10(num)<<endl;
}

void PrintLog10(double num, double logwf) {
  cout<<"c s log10-estimate "<<log10(num)+logwf<<endl;
}

void PrintLog10(const mpfr::mpreal& num) {
  cout<<"c s log10-estimate "<<mpfr::log10(num)<<endl;
}

void PrintExact(const mpz_class& num) {
  cout<<"c s exact arb int "<<num<<endl;
}

void PrintExact(const mpfr::mpreal& num) {
  cout<<"c s exact arb float "<<num<<endl;
}

void PrintDouble(double num) {
  cout<<"c s exact double float "<<num<<endl;
}

int main(int argc, char *argv[]) {
    bool idemp_mode = false;
    string input_file;
    string techniques = "G";
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "-m") == 0) {
            if (argc <= i + 1) {
                cout << " wrong parameters" << endl;
                return -1;
            } else {
                if (strcmp(argv[i+1], "idemp") == 0) {
                    idemp_mode = true;
                }
                else if (strcmp(argv[i+1], "general") != 0) {
                    cout << " mode not recognized" << endl;
                    return -1;
                }
                i++;
            }
        }
        else if (strcmp(argv[i], "-t") == 0) {
            if (argc <= i + 1) {
                cout << " wrong parameters" << endl;
                return -1;
            } else {
                techniques = argv[i+1];
                i++;
            }
        }
        else {
            input_file = argv[i];
        }
    }
    sspp::Instance ins(input_file, true);
    sspp::Preprocessor ppp;
    ins = ppp.Preprocess(ins, techniques, idemp_mode);
    ins.UpdClauseInfo();
    cout<<"c o Preprocessed. Vars: "<<ins.vars<<" Clauses: "<<ins.clauses.size()<<" Free vars: "<<ppp.FreeVars()<<endl;
    ins.Print(cout);
    return 0;
}

