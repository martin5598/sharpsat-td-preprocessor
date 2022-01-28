#pragma once

#include "utils.hpp"
#include "instance.hpp"

#include <map>

namespace sspp {
class Preprocessor {
 public:
	// applies the preprocessing techniques in `techniques` to instance `ins`
 	Instance Preprocess(Instance ins, const string& techniques, bool idemp_mode_);
	// checks if `techniques` is a valid string of preprocessing techniques
	// if so they are applied to the instance given by vars_, clauses_
 	Instance Preprocess(int vars_, vector<vector<Lit>> clauses_, string techniques, bool idemp_mode_);
 	// returns the number of variables which are unconstrained
	int FreeVars() const;
 	void SetMaxGTime(double time);
 	void SetMaxSparsTime(double time);
 private:
	// applies the preprocessing techniques in `techniques`
	// until a fixed point is reached
 	bool DoTechniques(const string& techniques, int l, int r);
 	bool EliminateDefSimplicial();
	// merges any two equivalent literals whose variables cooccur in some clause
	// uses a sat oracle call to determine equivalence
	// removes subsumed clauses afterwards
 	void MergeAdjEquivs();
	// checks for implied clauses using a sat oracle call
	// and removes them
  void Sparsify();
	// returns the preprocessed instance using the original variable indices
 	Instance MapBack();
	// returns a minimal unsat instance
 	Instance UnsatInst();
	// check for backbone literals by checking if ins && l is unsat
	// uses a sat oracle call and applies tightening and subsuming afterwards
 	void BackBone();
	// removes literal l from clause cls if cls\{l} is implied
	// uses unit propagation and applies tightening and subsuming afterwards
 	void PropStren();
	// checks for subsumed clauses (afaik it uses a subset check)
	// and removes them
 	void Subsume();
	// check for backbone literals by checking if ins && l is unsat
	// uses unit propagation and applies tightening and subsuming afterwards
 	void FailedLiterals();
	// removes all the unit clauses
	// and remembers the value of the backbone literal in assign
 	void TakeUnits(vector<vector<Lit>>& cls);
	// ensures that the variable indices do not have holes
	// and simplifies away the backbone literals
 	void MapClauses(vector<vector<Lit>>& cls, Var& nvars, vector<Var>& map_to);
	// removes duplicate clauses and applies unit propagation
	// if loop is true recursively until fixed point
 	void Tighten();
 	int vars = 0;
 	vector<vector<Lit>> clauses, learned_clauses;
 	Timer timer;

 	int orig_vars = 0;
 	vector<Var> var_map;
	// backbone literals
 	// 1 positive 2 negative
 	vector<char> assign;
 	bool unsat = false;

 	bool weighted = false;
 	bool idemp_mode = false;
 	vector<vector<double>> weights;
 	int free_vars = 0;

 	double max_g_time = 1e9;
 	double max_s_time = 1e9;

 	Timer g_timer;
 	Timer s_timer;

 	void eqdfs(Lit lit, Lit e, const vector<vector<Lit>>& eq, vector<Lit>& eqc);
};
inline bool ValidTechniques(const string& techniques, bool weighted) {
	int d = 0;
	for (char c : techniques) {
		if (c == '[') {
			d++;
		} else if (c == ']') {
			d--;
			if (d < 0) return false;
		} else if (c == 'F' // failed literals by propagation
			      || c == 'P' // vivification by propagation
			      || c == 'V' // complete vivification
			      || c == 'S' // sparsification
			      || c == 'E') { // equivalence merging
			// ok
		} else if (c == 'G') { // B+E
			// ok
		} else if (c == 'I' && !weighted) { // Inc B+E
			// ok
		} else {
			return false;
		}
	}
	return d == 0;
}
} // namespace sspp
