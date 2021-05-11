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
#include <set>
#include "parser.h"
#define _f first
#define _s second
using namespace std;

class solver{
    int num_var; // number of variable
    vector< vector<int> >  clauses;

    int sat;
    vector<int> value;

    vector< vector<int> > pos_watch;
    vector< vector<int> > neg_watch;
    vector< pair<int, int> > watched_in_clause;

    vector<double> counter; // which variable first

    stack<int> s_assign;
    vector< pair<int, int> > level_w;

public:
    void init(char* cnf_in);
    void create_watch_list();
    void VSIDS_init();

    void solve();
    void result(char* cnf_name);

    // -1 continue, >=0 conflict clause
    int BCP(int assignment, int now_level);
    int first_UIP(vector<int> C, int now_level);

    void VSIDS_update();
    int VSIDS_decide();

    int back_to(int level);
    void assign(int lit, int val, int level, int c);
};

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

// initialization
void solver::init(char* cnf_in){
    // parse the file
    parse_DIMACS_CNF(clauses, num_var, cnf_in);
    sat = 0;
    value.resize(num_var + 1);
    value[0] = -1;
    level_w.resize(num_var + 1);
    // 
    create_watch_list();
    VSIDS_init();
}

// watch first 2 literals of each clause
void solver::create_watch_list(){
    pos_watch.resize(num_var + 1);
    neg_watch.resize(num_var + 1);
    watched_in_clause.resize(clauses.size());
    for(int i = 0; i < clauses.size(); i++){
        if(clauses[i].size() >= 1){
            watched_in_clause[i]._f = clauses[i][0];
            if(clauses[i][0] > 0) pos_watch[clauses[i][0]].push_back(i);
            else neg_watch[abs(clauses[i][0])].push_back(i);
        }
        if(clauses[i].size() >= 2){
            watched_in_clause[i]._s = clauses[i][1];
            if(clauses[i][1] > 0) pos_watch[clauses[i][1]].push_back(i);
            else neg_watch[abs(clauses[i][1])].push_back(i);
        }
    }
}

// initialize counter
void solver::VSIDS_init(){
    counter.resize(2 * num_var + 1);

    for(int i = 0; i < clauses.size(); i++){
        for(int j = 0; j < clauses[i].size(); j++){
            if(clauses[i][j] > 0){
                counter[clauses[i][j]<<1] += 1.0;
            }
            else{
                counter[(abs(clauses[i][j])<<1)-1] += 1.0;
            }
        }
    }
}

// Conflict Driven Clause Learing Method
int solver::first_UIP(vector<int> C, int now_level){
    vector<int> inC(counter.size());
    for(int i = 0; i < C.size(); i++){
        int tmp = abs(C[i])<<1;
        if(C[i] < 0) tmp -= 1;
        inC[tmp] = 1;
    }

    while(1){
        int meet = 0, end = 1;
        // meet: lit. of current level
        // end: ending flag
        int idx = 0;
        // idx: index of meet

        for(int i = 0; i < C.size(); i++){
            if(level_w[abs(C[i])]._f == now_level){
                if(!meet){
                    meet = abs(C[i]);
                    idx = i;
                }
                else if(meet == abs(C[i])){
                    continue;
                }
                else{
                    if(level_w[meet]._s == -1){
                        meet = abs(C[i]);
                        idx = i;
                    }
                    end = 0;
                    break;
                }
            }
        }

        if(end){
            int max = 0;
            int idx2 = -1;
            for(int i = 0; i < C.size(); i++){
                if(max <= level_w[abs(C[i])]._f && level_w[abs(C[i])]._f < now_level){
                    max = level_w[abs(C[i])]._f;
                    idx2 = i;
                }
            }

            // learn clause
            if(1){

                clauses.push_back(C);
                watched_in_clause.push_back(make_pair(0, 0));

                watched_in_clause[clauses.size() - 1]._f = C[idx];
                if(C[idx] > 0) pos_watch[C[idx]].push_back(clauses.size() - 1);
                else neg_watch[abs(C[idx])].push_back(clauses.size() - 1);

                if(idx2 >= 0){
                    watched_in_clause[clauses.size() - 1]._s = C[idx2];
                    if(C[idx2] > 0) pos_watch[C[idx2]].push_back(clauses.size() - 1);
                    else neg_watch[abs(C[idx2])].push_back(clauses.size() - 1);
                }
            }
            else{
                return now_level;
            }
            return max;
        }

        int cla = level_w[meet]._s;

        C[idx] = C[C.size()-1];
        C.pop_back();
        for(int i = 0; i < clauses[cla].size(); i++){
            int tmp = abs(clauses[cla][i])<<1;
            if(clauses[cla][i] < 0) tmp -= 1;

            if(!inC[tmp] && abs(clauses[cla][i]) != meet){
                C.push_back(clauses[cla][i]);
                inC[tmp] = 1;
            }
        }
        inC[meet<<1] = 0;
        inC[(meet<<1)-1] = 0;
    }
}

// update counter
void solver::VSIDS_update(){
    for(int i = 1; i < counter.size(); i++) counter[i] *= 0.95;
    int idx = clauses.size()-1;
    for(int i = 0; i < clauses[idx].size(); i++){
        int lit = clauses[idx][i];
        if(lit > 0) counter[lit<<1] += 1.0;
        else counter[(abs(lit)<<1)-1] += 1.0;
    }
}

// choose one literal & value to assign
int solver::VSIDS_decide(){
    double max = -1.0;
    int lit = 0;
    for(int i = 1; i < counter.size(); i++){
        if(counter[i] > max){
            int a = (i+1)>>1;

            if(!value[a]){
                lit = a;
                if(!i%2) lit *= (-1);
                max = counter[i];
            }
        }
    }
    return lit;
}

// assign value to literal
void solver::assign(int lit, int val, int level, int c){
    value[lit] = val;
    level_w[lit]._f = level;
    level_w[lit]._s = c;
    s_assign.push(lit);
}

// entrance of solver
void solver::solve(){
    int level = 0;
    int decided = 0;
    int wait = 0;
    while(1){
        // check for unit clause

        if(!level){
            for(int i = 0; i < clauses.size(); i++){
                if(clauses[i].size() == 1){
                    int lit = abs(clauses[i][0]);
                    int val = clauses[i][0] > 0 ? 1 : -1;
                    if(!value[lit]){
                        if(BCP(clauses[i][0], 0) >= 0){
                            sat = 0;
                            return;
                        }
                    }
                    else if(value[lit] == val * -1){
                        sat = 0;
                        return;
                    }
                }
            }
        }
        else{
            int assignment;
            if(decided){
                assignment = decided;
                decided = 0;
            }
            else assignment = VSIDS_decide();
            if(!assignment){
                sat = 1;
                return;
            }

            int conflict = BCP(assignment, level);
            if(conflict >= 0){    
                
                // learn new clause
                // back = level to go back
                int back = first_UIP(clauses[conflict], level);

                // update counter

                if(back == level){
                    back_to(back);
                    decided = assignment * -1;
                    continue;
                }
                else if (back == 0){
                    decided = 0;
                    back_to(0);
                    level = 0;
                    continue;
                }
                decided = back_to(back);
                VSIDS_update();
                level = back;
                continue;
            }
        }
        level ++;
    }
}

// go back
int solver::back_to(int level){
    int ret = -1;
    while(!s_assign.empty() && level_w[s_assign.top()]._f >= level){
        ret = s_assign.top();
        value[s_assign.top()] = 0;
        level_w[s_assign.top()] = make_pair(0, 0);
        s_assign.pop();
    } 
    return ret;
}

// BCP using 2 literal watching
int solver::BCP(int assignment, int now_level){
    stack< pair<int, int> > imply;
    // implied value, source clause
    imply.push(make_pair(assignment, -1));

    while(!imply.empty()){
        assignment = imply.top()._f;
        int c = imply.top()._s; // source clause
        imply.pop();
        int val = assignment > 0 ? 1 : -1; //implied value
        int lit = abs(assignment); // implied literal

        if(value[lit]) continue; // if already assigned -> don't assign again
        assign(lit, val, now_level, c);

        if(val > 0){
            // assigned value = 1 -> watch the negative list
            // for clauses in neg_watch
            for(int i = 0; i < neg_watch[lit].size(); i++){
                c = neg_watch[lit][i]; // clause index
                int done = 0;
                
                int another; // the other watched literal
                if(watched_in_clause[c]._f == assignment * (-1)) another = watched_in_clause[c]._s;
                else another = watched_in_clause[c]._f;
                // the value of the other watched clause
                int v = value[abs(another)];
                if(another < 0) v *= -1;
                // resolved clause
                if(v > 0) continue;

                // find a new literal to watch
                for(int j = 0; j < clauses[c].size(); j++){
                    // for literal in that clause

                    if((!value[abs(clauses[c][j])] // assigned
                        || value[abs(clauses[c][j])] == (clauses[c][j] > 0 ? 1 : -1) ) //resolved
                    && clauses[c][j] != watched_in_clause[c]._f // not watched
                    && clauses[c][j] != watched_in_clause[c]._s){
                        // remove from neg watch
                        neg_watch[lit][i] = neg_watch[lit][neg_watch[lit].size()-1];
                        neg_watch[lit].pop_back();
                        // add new watched lit to list
                        if(clauses[c][j] > 0)
                            pos_watch[clauses[c][j]].push_back(c);
                        else neg_watch[abs(clauses[c][j])].push_back(c);

                        // chang watched_in_clause
                        if(watched_in_clause[c]._f == assignment * (-1)){
                            watched_in_clause[c]._f = clauses[c][j];
                        }
                        else{
                            watched_in_clause[c]._s = clauses[c][j];
                        }
                        done = 1;
                        i--; //

                        break;
                    }
                }
                if(done) continue; // unassiggned or resolved
                
                if(!v){
                    // unit clause
                    imply.push(make_pair(another, c));
                }
                else if(v < 0){ 
                    return c;
                }
            }
        }
        else{
            // assigned value = 1 -> watch the positive list
            // for clauses in pos_watch

            for(int i = 0; i < pos_watch[lit].size(); i++){
                // index of current clause
                c = pos_watch[lit][i];
                int done = 0;

                int another; // the other watched lit
                if(watched_in_clause[c]._f == assignment * (-1)) another = watched_in_clause[c]._s;
                else another = watched_in_clause[c]._f;
                // vlaue of the other watched
                int v = value[abs(another)];
                if(another < 0) v *= -1;

                if(v > 0) continue; // resolved

                for(int j = 0; j < clauses[c].size(); j++){
                    // for literal in this clause
                    if((!value[abs(clauses[c][j])]  // not assigned
                        || value[abs(clauses[c][j])] == (clauses[c][j] > 0 ? 1 : -1) ) // resolved
                    && clauses[c][j] != watched_in_clause[c]._f // not watched
                    && clauses[c][j] != watched_in_clause[c]._s){

                        // remove from pos watch
                        pos_watch[lit][i] = pos_watch[lit][pos_watch[lit].size()-1];
                        pos_watch[lit].pop_back();
                        // add new watched lit to list
                        if(clauses[c][j] > 0)
                            pos_watch[clauses[c][j]].push_back(c);
                        else neg_watch[abs(clauses[c][j])].push_back(c);

                        // chang watched_in_clause
                        if(watched_in_clause[c]._f == assignment * (-1)){
                            watched_in_clause[c]._f = clauses[c][j];
                        }
                        else{
                            watched_in_clause[c]._s = clauses[c][j];
                        }
                        done = 1;
                        i--; //
                        break;
                    }
                }
                if(done) continue; // unassiggned or resolved
                
                if(!v){
                    // unit clause
                    imply.push(make_pair(another, c));
                }
                else if(v < 0){ 
                    return c;
                }
            }
        }
    }
    // finished without conflict
    return -1;
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

    if(!sat) cout << "UNSAT\n";
    else cout << "SAT\n";

    file.close();
}