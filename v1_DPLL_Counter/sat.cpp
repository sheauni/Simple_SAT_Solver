#include <iostream>
#include <vector>
#include <stack>
#include <queue>
#include <utility>
#include <cmath>
#include <algorithm>
#include <cstdio>
#include <fstream>
#include <cstring>
#include "parser.h"
#define fir first
#define sec second
using namespace std;

class solver{
    int num_var; // number of variable
    vector<int> heuristic; // which variable first
    vector< vector<int> >  clauses;

    // for every clause
    vector< pair<int, int> >  counter;
    // for every variable
    vector<int> value;
    vector<vector<int> > pos, neg;
    
    queue< pair<int, int> > implication;
    stack< pair<int, int> > given_value;
    
    int sat; //result

public:
    void init(char* cnf_in);

    void solve();
    int  DPLL(int now_layer);
    void assign(int now_layer, int var, int val);
    void back(int layer);

    void result(char* cnf_name);
};

vector<double> score; // for heuristic (J-W score)
bool cmp(const int &l, const int &r){
    return score[l] > score[r];
}

int main(int argc, char *argv[]){
    if(argc != 2){
        cout << "Something wrong!" << endl;
        return 0;
    }
    solver s;
    s.init(argv[1]);
    s.solve();
    s.result(argv[1]);
}

/*** Read Input & Initialization ***/
void solver::init(char* cnf_in){
    // parse the file
    parse_DIMACS_CNF(clauses, num_var, cnf_in);
    counter.resize(clauses.size());
    sat = 0;

    value.resize(num_var + 1);
    pos.resize(num_var + 1);
    neg.resize(num_var + 1);
    for(int i = 0; i < clauses.size(); i++){
        // clauses with one literal -> treat as implication
        if(clauses[i].size() == 1){
            int val = clauses[i][0] > 0 ? 1 : -1;
            int var = abs(clauses[i][0]);
            implication.push(make_pair(var, val));
        }
        // push to vector pos or neg
        for(int j = 0; j < clauses[i].size(); j++){
            if(clauses[i][j] > 0) pos[clauses[i][j]].push_back(i);
            else neg[abs(clauses[i][j])].push_back(i);
        }
    }

    // J-W score
    score.resize(num_var + 1);
    score[0] = -1.0;
    for(int i = 1; i <= num_var; i++){
        for(int j = 0; j < pos[i].size(); j++){
            score[i] += pow(2, clauses[ pos[i][j] ].size() * (-1));
        }
        for(int j = 0; j < neg[i].size(); j++){
            score[i] += pow(2, clauses[ neg[i][j] ].size());
        }
    }
    // sort variable according to J-W score
    heuristic.resize(num_var + 1);
    for(int i = 0; i <= num_var; i++) heuristic[i] = i;
    sort(heuristic.begin(), heuristic.end(), cmp);
}

/*** Entrance ***/
void solver::solve(){
    sat = DPLL(0);
}

/*** DPLL ***/
int solver::DPLL(int now_layer){
    /* BCP */
    while(!implication.empty()){
        pair<int, int> imp = implication.front();
        implication.pop();

        if(value[imp.fir] != 0 && value[imp.fir] != imp.sec){
            // conflict
            return 0;
        }
        if(value[imp.fir] != 0 && value[imp.fir] == imp.sec)
            continue;

        // assign and check for implication
        assign(now_layer, imp.fir, imp.sec);
    }

    /* next variable to DECIDE */
    int ptr;
    for(int i = 0; i < heuristic.size(); i++){
        if(i == heuristic.size() - 1) return 1; // sat
        if(value[heuristic[i]] == 0){
            ptr = heuristic[i];
            break;
        }
    }

    now_layer += 1;

    while(!implication.empty()) implication.pop();
    assign(now_layer, ptr, 1);
    if(DPLL(now_layer)) return 1;
    back(now_layer);

    while(!implication.empty()) implication.pop();
    assign(now_layer, ptr, -1);
    if(DPLL(now_layer)) return 1;
    back(now_layer);

    return 0;
}

/*** Assign & Check for Implication ***/
void solver::assign(int now_layer, int var, int val){
    value[var] = val;
    given_value.push(make_pair(now_layer, var));
    // case: assign 1 to var
    if(val > 0){
        // positive literal = 1
        for(int i = 0; i < pos[var].size(); i++){
            counter[pos[var][i]].sec += 1;
        }
        // negative literal = -1
        for(int i = 0; i < neg[var].size(); i++){
            int nowc = neg[var][i];
            counter[nowc].fir += 1;

            // implication
            if(counter[nowc].fir == clauses[nowc].size() - 1
            && !counter[nowc].sec){
                int impval = 0;
                for(int j = 0; j < clauses[nowc].size(); j++){
                    if(!value[ abs(clauses[nowc][j]) ]){
                        if(clauses[nowc][j] > 0) impval = 1;
                        else impval = -1;
                        implication.push(make_pair(abs(clauses[nowc][j]), impval));
                        break;
                    }
                }
            }
        }
    }
    // case: assign -1 to var
    else{
        // positive literal = -1
        for(int i = 0; i < pos[var].size(); i++){
            int nowc = pos[var][i];
            counter[nowc].fir += 1;

            // implication
            if(counter[nowc].fir == clauses[nowc].size() - 1
            && !counter[nowc].sec){
                int impval = 0;
                for(int j = 0; j < clauses[nowc].size(); j++){
                    if(!value[ abs(clauses[nowc][j]) ]){
                        if(clauses[nowc][j] > 0) impval = 1;
                        else impval = -1;
                        implication.push(make_pair(abs(clauses[nowc][j]), impval));
                        break;
                    }
                }
            }
        }
        // negative literal = 1
        for(int i = 0; i < neg[var].size(); i++){
            counter[neg[var][i]].sec += 1;
        }
    }
}

/*** Get Back to Last Layer ***/
void solver::back(int layer){
    while(!given_value.empty() && given_value.top().fir == layer){
        int var = given_value.top().sec;
        int val = value[var];
        given_value.pop();
        
        value[var] = 0;
        if(val > 0){
            for(int i = 0; i < pos[var].size(); i++){
                counter[pos[var][i]].sec -= 1;
            }
            for(int i = 0; i < neg[var].size(); i++){
                counter[neg[var][i]].fir -= 1;
            }
        }
        else{
            for(int i = 0; i < pos[var].size(); i++){
                counter[pos[var][i]].fir -= 1;
            }
            for(int i = 0; i < neg[var].size(); i++){
                counter[neg[var][i]].sec -= 1;
            }
        }
    }
}

/*** Output file ***/
void solver::result(char* cnf_name){
    int l = strlen(cnf_name);
    cnf_name[l-3] = 's';
    cnf_name[l-2] = 'a';
    cnf_name[l-1] = 't';

    fstream file;
    file.open(cnf_name, ios::out);

    if(sat){
        file << "s SATISFIABLE\n";
        file << "v";
        for(int i = 1; i <= num_var; i++) file << " " << i * value[i];
        file << "\n";
    }
    else file << "s UNSATISFIABLE\n";

    file.close();
}