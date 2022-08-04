#include <vector>
#include <set>
#include "problem.h"
#include <string>
#include <map>
#include <stack>
#include <cstring>
#include <unordered_set>
#include <iostream>
#include <queue>
#include <climits>
#include <algorithm>
#include <sstream>
#include <unordered_map>
#include <bitset>
#include <chrono>
#include <deque>
using namespace std;
#include <stdlib.h>
#include <stdio.h>
#include <strings.h>
#include "problem.h"
#define LM_CUT true
#define MAX_FACTS 120
#define OP 1
#define DISTANCES 2
#define HMX 3
#define VISITED 4
// I created a vector of operator costs globally for the purpose of LM-Cut, where I rewrite operator costs
std::vector<int> operator_costs;
// Map that stores most A-star relevant data such as pre-computed heuristics, operators linked with states, distances and whether said state was visited
std::unordered_map<int, std::unordered_map<std::bitset<MAX_FACTS>, int>> search_map;
// Struct used to search 
typedef struct search_strips search_strips_t;
typedef struct hmax_node hmax_t;
struct search_strips{
    int distance;
    std::bitset<MAX_FACTS> bits;
};
struct hmax_node{
    int hmax;
    std::vector<int> deltas;
};
 
struct compare_stripses{
    bool operator() (search_strips_t * f, search_strips_t * s){
        return f->distance>s->distance;
    }
};
static void my_read_set(FILE *fin, const char *path, int *size, int **values)
{
    /* This function is identical to the one provided in "problem.h"*/
    if (fscanf(fin, "%d", size) != 1){
        fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
        exit(-1);
    }
    *values = (int *)malloc(sizeof(int) * *size);
    for (int i = 0; i < *size; ++i){
        if (fscanf(fin, "%d", (*values) + i) != 1){
            fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
            exit(-1);
        }
    }
}
 
void Freeing_strips(strips_t *strips)
{
    /* This function is identical to the one provided in "problem.h"*/
    for (int i = 0; i < strips->num_facts; ++i){
        if (strips->fact_names[i] != NULL)
            free(strips->fact_names[i]);
    }
    if (strips->fact_names != NULL)
        free(strips->fact_names);
 
    for (int i = 0; i < strips->num_operators; ++i){
        strips_operator_t *op = strips->operators + i;
        if (op->name != NULL)
            free(op->name);
        if (op->pre != NULL)
            free(op->pre);
        if (op->add_eff != NULL)
            free(op->add_eff);
        if (op->del_eff != NULL)
            free(op->del_eff);
    }
    if (strips->operators != NULL)
        free(strips->operators);
}
 
struct compare_number_pairs{
    bool operator() (const std::pair<int, int> f, const std::pair<int, int> s){
        return f.first>s.first;
    }
};
  
void print_vector(std::vector<int> v){
    for(auto i: v)cout<<i<<" ";
        cout<<endl;
}
  
void print_bitset(std::bitset<MAX_FACTS> in){
    for(int i = 0; i < MAX_FACTS; i++){
        if(in[i])cout<<i<<" ";
    }
    cout<<endl;
}
 
///////////////////// Checked /////////////////////////////////
hmax_t * hmx(std::vector<int> vec, strips_t *p){
    /* Function returning the value of the hmax heuristic */
    std::vector<int> delta(p->num_facts,INT32_MAX/2); // checked
    for(int i = 0; i < (int)vec.size(); i++){
        delta[vec[i]] = 0;
    }
    //6
    std::unordered_map<int, int>U;
    // 3-5
    for(int i = 0; i < p->num_operators; i++){
        U[i] = p->operators[i].pre_size;   // 6. manually checked
        if(p->operators[i].pre_size == 0){
            for(int x = 0; x < p->operators[i].add_eff_size; x++){
                if(delta[p->operators[i].add_eff[x]]> p->operators[i].cost)delta[p->operators[i].add_eff[x]] = p->operators[i].cost;
            }   
        }
    }
    // 7. 
    std::bitset<MAX_FACTS>C;
    // s_goal
    std::bitset<MAX_FACTS> s_goal_bits;
    for(int i = 0; i < p->goal_size; i++){
        s_goal_bits[p->goal[i]] =1;
    }
    // saving all facts into F
    std::set<std::pair<int, int>>F_set;
    for(int i = 0; i < p->num_facts; i++){
        F_set.insert(std::make_pair(delta[i], i));
    }
    // Vector of all operators preconditions to keep tabs on what is which precondition
    std::vector<std::bitset<MAX_FACTS>>operator_preconditions; 
    for(int i = 0; i < p->num_operators; i++){
        std::bitset<MAX_FACTS>current;
        for(int x = 0; x < p->operators[i].pre_size;x++){
            current[p->operators[i].pre[x]] = 1;
        }
        operator_preconditions.push_back(current);
    }
    while((C & s_goal_bits) != s_goal_bits){ // 8. 
        auto curr = F_set.begin(); // 9. 
        F_set.erase(curr);
        int k = curr->second;
        C[k] = 1; // 10.
        // 11.
        for(int i = 0; i < p->num_operators; i++){ // 11. start
            if(operator_preconditions[i][k] == 1){ // 11. end --- toto musime rozepsat...delat si vektory vsech preconditions or something
                U[i] = U[i]-1; // 12. 
                if(U[i] == 0){
                    for(int x = 0; x < p->operators[i].add_eff_size; x++){
                        auto tmp = std::min(delta[p->operators[i].add_eff[x]], (p->operators[i].cost+delta[k]));
                        if(tmp != delta[p->operators[i].add_eff[x]]){ 
                            // pokud je v F_setu, tak ji vymenit
                            if(F_set.erase(std::make_pair(delta[p->operators[i].add_eff[x]], p->operators[i].add_eff[x]))){
                                F_set.insert(std::make_pair(tmp, p->operators[i].add_eff[x]));
                            }
                            delta[p->operators[i].add_eff[x]] = tmp;
                        }  
                    }
                }
            }
        }  
    }
    int hmax = INT_MIN;
    for(int i =0; i < p->goal_size; i++){
        hmax = std::max(hmax, delta[p->goal[i]]);
    }
    hmax_t * current = new hmax_node;
    current->hmax = hmax;
    current->deltas = delta;
    return current;
}
///////////////////////////////////////////////  NEW  ////////////////////////////////////////////
// napad je, prepsat ten read, aby dva pointery ukazovali na stejne misto v pameti
void mystripsRead(strips_t *strips, strips_t* my_strip,const char *path)
{
    FILE *fin;
    char name[256];
 
    bzero(strips, sizeof(*strips));
    fin = fopen(path, "r");
    if (fin == NULL){
        fprintf(stderr, "Error: Could not read `%s'\n", path);
        exit(-1);
    }
 
    if (fscanf(fin, "%d", &strips->num_facts) != 1){
        fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
        exit(-1);
    }
    my_strip->num_facts = strips->num_facts+2;
 
    strips->fact_names = (char **)malloc(sizeof(char *) * strips->num_facts);
    my_strip->fact_names = (char **)malloc(sizeof(char *) * strips->num_facts+2);
    for (int i = 0; i < strips->num_facts; ++i){
        if (fscanf(fin, "\n%[^\n]", name) != 1){
            fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
            exit(-1);
        }
        strips->fact_names[i] = (char *)malloc(strlen(name) + 1);
        my_strip->fact_names[i] = (char *)malloc(strlen(name) + 1);
        memcpy(strips->fact_names[i], name, strlen(name) + 1);
        memcpy(my_strip->fact_names[i], name, strlen(name) + 1);
 
    }
    my_strip->fact_names[strips->num_facts] = (char*)"I";
    my_strip->fact_names[strips->num_facts+1] = (char*)"G";
 
    my_read_set(fin, path, &strips->init_size, &strips->init);
    my_read_set(fin, path, &strips->goal_size, &strips->goal);
    my_strip->init_size = 1;
    my_strip->goal_size = 1;
    my_strip->goal = (int*)malloc(sizeof(int));
    my_strip->goal[0] = strips->num_facts+1;
      
    my_strip->init = (int*)malloc(sizeof(int));
    my_strip->init[0] = my_strip->goal[0]-1;
      
     
    if (fscanf(fin, "%d", &strips->num_operators) != 1){
        fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
        exit(-1);
    }
    my_strip->num_operators = strips->num_operators+2;
 
    strips->operators = (strips_operator_t *)malloc(sizeof(strips_operator_t)
                                                      * strips->num_operators);
    my_strip->operators = (strips_operator_t *)malloc(sizeof(strips_operator_t)
                                                      * (strips->num_operators+2));
    for (int i = 0; i < strips->num_operators; ++i){
        strips_operator_t *op = strips->operators + i;
        if (fscanf(fin, "\n%[^\n]", name + 1) != 1){
            fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
            exit(-1);
        }
        name[0] = '(';
        int len = strlen(name);
        name[len] = ')';
        name[len + 1] = 0x0;
        op->name = (char *)malloc(strlen(name) + 1);
        memcpy(op->name, name, strlen(name) + 1);
        my_read_set(fin, path, &op->pre_size, &op->pre);
        my_read_set(fin, path, &op->add_eff_size, &op->add_eff);
        my_read_set(fin, path, &op->del_eff_size, &op->del_eff);
        if (fscanf(fin, "%d", &op->cost) != 1){
            fprintf(stderr, "Error: Invalid STRIPS format in `%s'\n", path);
            exit(-1);
        }
        my_strip->operators[i] = *op;
    }
     // start operator 
    strips_operator_t *s_op = &my_strip->operators[strips->num_operators];
    s_op->name = (char*)"start_operator";
    s_op->cost = 0;
    s_op->pre_size = 1;
    s_op->pre = (int*)malloc(sizeof(int));//new int[1];
    s_op->pre[0] = strips->num_facts;
    s_op->add_eff_size = strips->init_size;
    s_op->add_eff = strips->init;
    s_op->del_eff_size = 0;
    s_op->del_eff_size = 0;
    // Initiate search map 
    std::unordered_map<std::bitset<MAX_FACTS>, int>a;
    search_map[OP]= search_map[DISTANCES] = search_map[HMX] = search_map[VISITED] = a;
    // terminal operator
    strips_operator_t *t_op = &my_strip->operators[strips->num_operators+1];
    t_op->name = (char*)"terminal_operator";
    t_op->cost = 0;
    t_op->pre = strips->goal;
    t_op->pre_size =strips->goal_size;
    t_op->add_eff = (int*)malloc(sizeof(int)*1);
    t_op->add_eff[0] = strips->num_facts+1;
    t_op->del_eff_size = 0;
    t_op->del_eff = (int*)malloc(sizeof(int));
    t_op->del_eff[0] = 1;
    t_op->add_eff_size = 1;
    fclose(fin);
}
 
void check_p(strips_t * p){
    cout<<"********************************************************************"<<endl;
        cout<<"********************************************************************"<<endl;
  
    cout<<"********************************************************************"<<endl;
  
    cout<<"********************************************************************"<<endl;
  
    cout<<endl;
    cout<<"num facts: "<<p->num_facts<<endl;
    cout<<"num operators: "<<p->num_operators<<endl;
    cout<<"Fact names "<<endl;
    for(int i = 0; i< p->num_facts; i++){
        printf("%s\n", p->fact_names[i]);
    }
    cout<<"Init size: "<<p->init_size<<endl;
    cout<<"Init: "<<endl;
    for(int x = 0; x < p->init_size; x++)cout<<p->init[x]<<" ";
        cout<<endl;
    cout<<"Goal size: "<<p->goal_size<<endl;
    cout<<"Goal: "<<endl;
    for(int x = 0; x < p->goal_size; x++)cout<<p->goal[x]<<" ";
        cout<<endl;
    for(int i = 0; i < p->num_operators; i++){
        cout<<"Name: "<<endl;
        printf("%s\n", p->operators[i].name);
  
        cout<<"Cost: "<<p->operators[i].cost<<endl;
        cout<<"Pre size : "<<p->operators[i].pre_size<<endl;
        cout<<"Pre: "<<endl;
        for(int x = 0; x < p->operators[i].pre_size; x++){
            cout<<p->operators[i].pre[x];
        }
        cout<<"Add eff size : "<<p->operators[i].add_eff_size<<endl;
        cout<<"Add: "<<endl;
        for(int x = 0; x < p->operators[i].add_eff_size; x++){
            cout<<p->operators[i].add_eff[x];
        }
        cout<<"Del eff size : "<<p->operators[i].del_eff_size<<endl;
        cout<<"Del: "<<endl;
        for(int x = 0; x < p->operators[i].del_eff_size; x++){
            cout<<p->operators[i].del_eff[x];
        }
  
  
    }
    return;
}
 
int my_lm_cut(std::vector<int> vec, strips_t * p){
    // 1. - 3. line of the algorithm
    // operator costs checked
    // s state checked on paper
    // start
    // Napraveni costu na 0
    p->operators[p->num_operators-2].cost = 0;
    p->operators[p->num_operators-1].cost = 0;
      
    int h_lm = 0; // 4th line
    //int i = 0; //6th line
    // adding add OPs for the start node
    std::vector<int> temp_start = vec; // maybe obsolete
    int counter = vec.size();
    p->operators[p->num_operators-2].add_eff_size = counter;
    p->operators[p->num_operators-2].add_eff = (int *)malloc(sizeof(int)*counter);
    for(int i = 0; i < counter; i++)p->operators[p->num_operators-2].add_eff[i] = temp_start[i];
    //int iteration = -1;
    //check_p(p);
    auto hmx_result = hmx(vec, p);
    int h_max = hmx_result->hmax;
    std::vector<int> delta = hmx_result->deltas;
    if (h_max>=9999999)return INT_MAX/2;
    while(h_max != 0){ //7th line
        // 8th line - Constructing a justification graph
        // first, we have to find supporters
        std::vector<std::pair<int, int>> supporters;
        //2. Lets find supporters
        int current_max;
        for(int i = 0; i < p->num_operators; i++){
            current_max = -INT_MAX;
            int max_idx = 0;
            for(int x = 0; x < p->operators[i].pre_size; x++){
                if(delta[p->operators[i].pre[x]]>current_max){
                    current_max = delta[p->operators[i].pre[x]];
                    max_idx = p->operators[i].pre[x];
                }
            }
            supporters.push_back(std::make_pair(max_idx, current_max));
        }
        // Now we have found supporters, so we can construct the justification graph (line 8): For every
        //operator and every fact from its add OP, we create an edge leading from the operator’s
        //supporter to that fact and we label the edge with the operator.
        //3. For every operator and their add OP we make an edge from operator's supporter to the add OP 
        // and we label the edge withh the operator
        std::vector<int> graph[p->num_facts][p->num_facts]; 
        for(int i = 0; i < p->num_operators; i++){
            for(int x = 0; x < p->operators[i].add_eff_size; x++){
                graph[supporters[i].first][p->operators[i].add_eff[x]].push_back(i);
            }
        } 
        // Proceeding with N* and N0 and the S-t cut
        // N*
        std::bitset<200> N_star_visited;
        std::deque<int> bfs;
        bfs.push_back(p->num_facts-1);
        while(!bfs.empty()){
            auto current = bfs.front();
            bfs.pop_front();
            if(N_star_visited[current] == 0){
                N_star_visited[current] = 1;
                for(int i = 0; i < p->num_facts;i++){
                    for(int x =0; x< graph[i][current].size();x++){
                        if(p->operators[graph[i][current][x]].cost == 0){
                            bfs.push_back(i);
                        }
                    }
                }
            }
        }
        // N0
        std::vector<int> landmark;
        int landmark_cost = 9999999;
        std::bitset<2000> N_0_visited;
        std::bitset<2000> landmark_visited;
        std::deque<int> bfs2;
        bfs2.push_back(p->init[0]);
        while(!bfs2.empty()){
            auto current = bfs2.front();
            bfs2.pop_front();
            if(N_0_visited[current] == 0){
                N_0_visited[current] = 1;
                for(int i = 0; i < p->num_facts;i++){
                    if(graph[current][i].empty())continue;
                    if(N_star_visited[i] == 0){
                        bfs2.push_back(i);
                    }else{
                        for(auto x : graph[current][i]){
                            if(p->operators[x].cost < landmark_cost)landmark_cost = p->operators[x].cost; // The cost of the landmark L = {o1, o2} is the minimum over the costs of operators from L,i.e., the cost is 1 (line 11).
                            if(landmark_visited[x] == 0){
                                landmark.push_back(x);
                                landmark_visited[x] =1;
                            }   
                        }
                    }   
                }
            }
        }
        h_lm = h_lm+landmark_cost; // line 11
        // We update the cost of the operators from L = {o1, o2,...} by substracting the cost of the landmark.
        for(auto o : landmark){
            p->operators[o].cost = p->operators[o].cost-landmark_cost;
        }
        auto rest = hmx(vec, p);
        delta = rest->deltas;
        h_max = delta[p->goal[0]];
    }
    // resetting costs
    for(int i = 0; i < p->num_operators; i++)p->operators[i].cost = operator_costs[i]; // this maybe move outside the function
    return h_lm;
}
///////////////////////////////////////////////  NEW  ////////////////////////////////////////////
std::bitset<MAX_FACTS> find_effect_bits(strips_operator_t successor, std::bitset<MAX_FACTS> current_bit_state){
    for(int i = 0; i < successor.add_eff_size; i++){
        current_bit_state[successor.add_eff[i]] = 1;
    }
    for(int i = 0; i < successor.del_eff_size; i++){
        current_bit_state[successor.del_eff[i]] = 0;
    }
    return current_bit_state;
}
void astar(std::bitset<MAX_FACTS> first_bit_vector, std::vector<int> first_vector,strips_t * p, strips_t * lm_strips) {
    // 1ST I CREATE A PRIORITY QUEUE OF OPEN SEARCH NODES
    std::priority_queue<search_strips_t *, std::vector<search_strips_t *>, compare_stripses> bit_open;
    // 2nd I create a search strips struct that looks like the initial state
    search_strips_t * current = new search_strips;
    current->distance = 0;
    current->bits = first_bit_vector;
    bit_open.push(current);
    std::bitset<MAX_FACTS>bit_goal;
    // OPERATOR COSTS FOR LM CUT and converting goal to bits
    for(int i = 0; i < p->num_operators; i++)operator_costs.push_back(p->operators[i].cost);
    for(int i = 0; i<p->goal_size; i++)bit_goal[p->goal[i]] = 1;
    std::unordered_map<std::bitset<MAX_FACTS>, std::bitset<MAX_FACTS>> bit_ancestors; // a budeme mit vektor techto classes a budoou se vyvolavat
    // vector tech classes a pak unordered ma jejichh vektoru of booleans a taky froonta cisel
    search_map[DISTANCES][first_bit_vector] = 0;
    search_map[OP][first_bit_vector] = -1;
 
    while(!bit_open.empty()){
        std::bitset<MAX_FACTS> current_bit_state = bit_open.top()->bits; // I take the current state in bits
        bit_open.pop();
        // 3. If we have already visited this one, we continue
        if(search_map[VISITED].find(current_bit_state) != search_map[VISITED].end())continue; // already visited
        // 4. We add it among our visited
        search_map[VISITED][current_bit_state] = -1; // can have more cache misses than vector
        // 5. we check if we are already in the goal state
        if((current_bit_state & bit_goal) == bit_goal){
            auto bit_curr = current_bit_state;
            std::vector<string> bit_preceeding_states;
            while(search_map[OP][bit_curr] != -1){
                bit_preceeding_states.push_back(p->operators[search_map[OP][bit_curr]].name);
                bit_curr = bit_ancestors[bit_curr];
            }
            std::reverse(bit_preceeding_states.begin(),bit_preceeding_states.end());
            cout<<";; Cost: "<<search_map[DISTANCES][current_bit_state]<<endl;
            cout<< ";; Init: "<<hmx(first_vector, p)->hmax<<endl;
            for(auto x : bit_preceeding_states)cout<<x<<endl;
            return;
        }
        // 6. we iterate over all operators
        for( int x = 0; x < p->num_operators; x++){
            bool operator_used = true;
            //7. if the current doesn't have the predispositions, we skip it
            for(int z = 0; z < p->operators[x].pre_size; z++){
                if (p->operators[x].pre_size > current_bit_state.count() or current_bit_state[p->operators[x].pre[z]]== 0){ // toto pujde bitove...zkontrolovat jestli je ma vsechnyyy...preconditions bitoveeee
                    operator_used = false;
                    break;
                }
            }
            //8. If it is satisfied, we unload the operator's 'add' into a new strips, delete dels and add to queue
            // a new node representing a state, provided it has not been expanded previously
            if(operator_used){
                search_strips_t * new_node = new search_strips;
                new_node->bits = find_effect_bits(p->operators[x], current_bit_state);
                int distance = p->operators[x].cost+search_map[DISTANCES][current_bit_state];
                if(search_map[VISITED].find(new_node->bits) != search_map[VISITED].end())continue;
                auto not_found = search_map[HMX].find(new_node->bits)!= search_map[HMX].end();
                if(distance>= search_map[DISTANCES][new_node->bits] and not_found)continue;
                if(not_found){
                    new_node->distance = search_map[HMX][new_node->bits];
                }else{
                    std::vector<int> v;
                    for(int i = 0; i<MAX_FACTS;i++){
                        if(new_node->bits[i] == 1)v.push_back(i);
                    }
                    new_node->distance = LM_CUT ? my_lm_cut(v, lm_strips) : hmx(v, p)->hmax;
                    search_map[HMX][new_node->bits] = new_node->distance;
                }
                bit_ancestors[new_node->bits] = current_bit_state; 
                search_map[DISTANCES][new_node->bits] = distance;
                search_map[OP][new_node->bits] = x;
                new_node->distance +=distance;
                bit_open.push(new_node);
            }
        }
    }
    return;
}
int main(int argc, char *argv[]){
    strips_t input_strips;
    strips_t alt_strips;
    if (argc != 3){
        fprintf(stderr, "Usage: %s problem.strips problem.fdr\n", argv[0]);
        return -1;
    }
    mystripsRead(&input_strips, &alt_strips,argv[1]);
    std::bitset<MAX_FACTS> initial_bitset;
    std::vector<int> vec;
    for(int i = 0; i < input_strips.init_size; i++){
        initial_bitset[input_strips.init[i]] = 1;  
        vec.push_back(input_strips.init[i]);
    } 
    std::vector<int> operator_costs;
    for(int i = 0; i < input_strips.num_operators; i++)operator_costs.push_back(input_strips.operators[i].cost);
    astar(initial_bitset, vec, &input_strips, &alt_strips);
    Freeing_strips(&input_strips);
    return 0;
}
