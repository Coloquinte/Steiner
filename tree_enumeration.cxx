/*
 * tree_enumeration.cxx
 *
 * Copyright 2013 Gabriel Gouvine <gabriel.gouvine@polytechnique.edu>
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 3 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston,
 * MA 02110-1301, USA.
 *
 *
 */

#include <vector>
#include <array>
#include <bitset>
#include <functional>
#include <algorithm>
#include <cmath>
#include <cassert>

#include <iostream>

struct edge{
    int f, s;
    edge(int a, int b){ f=a; s=b; }
};

struct tree{
    int n;
    std::vector<edge> edges;
    std::vector<int> prufer_representation;

    bool is_steiner_feasible() const{
        assert(edges.size() == n-1);
        assert(prufer_representation.size() == n-2);
        std::vector<int> before(n, 0), after(n, 0);
        for(edge e : edges){
            assert(e.f != e.s);
            if(e.f < e.s){
                after.at(e.f)++; before.at(e.s)++;
            }
            else{
                after.at(e.s)++; before.at(e.f)++;
            }
        }
        bool feasible = true;
        for(int i=0; i<n; ++i){
            if(std::abs(after[i] - before[i]) > 1 or (before[i] > after[i] and after[i] >= 1)){ // Else we could just move the vertical part to the left, increasing afteri[i] and decreasing before[i] with the same vertical length and a lower horizontal length
            //if(std::abs(after[i] - before[i]) > 1){
                feasible = false;
            }
        }
        return feasible;
    }
};

tree decode_prufer(std::vector<int> const & prufer_suite){
    int n = prufer_suite.size() + 2;
    tree ret;
    ret.n = n;

    std::vector<int> final_degrees(n, 1), degrees;
    for(int p : prufer_suite){
        final_degrees[p]++;
    }
    degrees = final_degrees;

    for(int p : prufer_suite){
        int i=0;
        while(degrees[i] != 1){
            assert(i < n);
            ++i;
        }
        ret.edges.push_back(edge(p, i));
        degrees[i]--;
        degrees[p]--;
    }
    int i=0;
    while(degrees[i] != 1){
        ++i;
        assert(i<n-1);
    }
    int j=i+1;
    while(degrees[j] != 1){
        ++j;
        assert(j<n);
    }
    ret.edges.push_back(edge(j, i));
    ret.prufer_representation = prufer_suite;
    return ret;
}

void generate_prufers(int n, int size, std::vector<int> & prufer_suite, std::vector<tree> & x_trees){
    assert(prufer_suite.size() == n-2);
    if(size == 0){
        auto T = decode_prufer(prufer_suite);
        if(T.is_steiner_feasible()){
            x_trees.push_back(T);
        }
    }
    else{
        for(int i=0; i<n; ++i){
            prufer_suite[size-1] = i;
            generate_prufers(n, size-1, prufer_suite, x_trees);
        }
    }
}

template<int n>
struct fixed_size_tree{
    static_assert(n < 256, "The size of the tree must be within unsigned char limits");
    static_assert(2 <= n, "The tree has too few pins");

    //// Secondary but useful data
    std::array<unsigned char, n-2> prufer_representation;
    std::array<unsigned char, n-1> costs;

    //// Important for Steiner calculation
    //std::array<unsigned char, n> degree;
    std::array<unsigned char, n-1> sorted_nodes; // The nodes sorted by order of becoming of degree 1 when removing nodes
    std::array<unsigned char, n-1> last_connexion; // When all previous nodes have been removed

    // This function greatly influences the number of trees that are kept after pruning!!!! I kept the best I came up with
    bool operator<(fixed_size_tree<n> const o) const{
        /*
        std::array<unsigned char, 2*n-2> connexions, o_connexions;
        for(int i=0; i<n-1; ++i){
            connexions[2*i] = sorted_nodes[i];
            connexions[2*i+1] = last_connexion[i];
            o_connexions[2*i] = o.sorted_nodes[i];
            o_connexions[2*i+1] = o.last_connexion[i];
        }
        return connexions < o_connexions;
        */
        return sorted_nodes < o.sorted_nodes || (sorted_nodes == o.sorted_nodes && last_connexion < o.last_connexion);
    }

    void get_costs(){
        for(unsigned char & c : costs){
            c = 0;
        }
        for(int i=0; i<n-1; ++i){
            int f = sorted_nodes[i]; int s = last_connexion[i]; // An edge between two nodes
            for(int i = std::min(f, s); i < std::max(f, s); ++i){ // Add to the cost on the path
                costs[i]++;
            }
        }
    }

};


template<int n>
struct lookup_struct{
    // First the positive influence for all of the entries (x then y), then the negative influence
    std::bitset<4*n - 8> cost;
    int tree_index;
};

template<int n>
fixed_size_tree<n> get_fixed(tree const T){
    fixed_size_tree<n> ret;
    static_assert(n >= 2, "Size should be greater than 1");
    assert(T.n == n);
    std::array<unsigned char, n> current_degrees;
    for(unsigned char & c : current_degrees){
        c = 0;
    }
    for(edge e : T.edges){
        assert(0 <= e.f && 0 <= e.s);
        assert(e.f < n && e.s < n);
        current_degrees[e.f]++;
        current_degrees[e.s]++;
    }

    int cnt = 0;
    for(unsigned char c : current_degrees){
        cnt += c;
        assert(c >= 1);
    }
    assert(cnt == 2*n - 2);
    assert(T.edges.size() == n-1);

    for(int i=0; i<n-2; ++i){
        ret.prufer_representation[i] = static_cast<unsigned char>(T.prufer_representation[i]);
    }
    
    for(int i=0; i<n-1; ++i){
        // Find first node of remaining degree exactly 1
        int k=0;
        while(true){
            if(current_degrees[k] == 1){
                break;
            }
            k++;
            assert(k<n);
        }
        ret.sorted_nodes[i] = static_cast<unsigned char>(k);

        // Find corresponding connexion and add it; decrement both degrees
        bool found = false;
        for(int j=0; j<n-1; ++j){
            if(T.edges[j].f == k){
                int other = T.edges[j].s;
                if(current_degrees[other] > 0){
                    assert(k != other);
                    ret.last_connexion[i] = static_cast<unsigned char>(other);
                    current_degrees[k]--;
                    current_degrees[other]--;
                    assert(!found);
                    found = true;
                }
            }
            else if(T.edges[j].s == k){
                int other = T.edges[j].f;
                if(current_degrees[other] > 0){
                    assert(k != other);
                    ret.last_connexion[i] = static_cast<unsigned char>(other);
                    current_degrees[k]--;
                    current_degrees[other]--;
                    assert(!found);
                    found = true;
                }
            }
        }
        assert(found);
    }
   
    ret.get_costs();
    return ret;
}


template<int n>
std::vector<lookup_struct<n> > get_optimal_costs(std::array<unsigned char, n> vertical_order, std::vector<fixed_size_tree<n> > const & x_connectivity){
    struct tmp_lookup_cost{
        std::array<unsigned char, 2*n - 2> cost;
        int tree_index;

        lookup_struct<n> to_struct() const{
            lookup_struct<n> ret;
            ret.tree_index = tree_index;
            for(int i=0; i<n-2; ++i){// positive x
                assert(std::abs(static_cast<int>(cost[i]) - static_cast<int>(cost[i+1])) <= 1);
                ret.cost[i] = (cost[i] > cost[i+1]);
            }
            for(int i=n-2; i<2*n-4 ; ++i){// positive y
                assert(std::abs(static_cast<int>(cost[i+1]) - static_cast<int>(cost[i+2])) <= 1);
                ret.cost[i] = (cost[i+1] > cost[i+2]);
            }
            for(int i=0; i<n-2; ++i){// negative x
                assert(std::abs(static_cast<int>(cost[i]) - static_cast<int>(cost[i+1])) <= 1);
                ret.cost[2*n-4 + i] = (cost[i] < cost[i+1]);
            }
            for(int i=n-2; i<2*n-4 ; ++i){// negative y
                assert(std::abs(static_cast<int>(cost[i+1]) - static_cast<int>(cost[i+2])) <= 1);
                ret.cost[2* n-4 + i] = (cost[i+1] < cost[i+2]);
            }
            return ret;
        }
    };

    std::vector<tmp_lookup_cost> current_best_costs;

    for(int ind = 0; ind < x_connectivity.size(); ind++){
        auto T = x_connectivity[ind];
        // x cost
        std::array<unsigned char, 2*n-2> new_cost;
        for(int i=0; i<n-1; ++i){
            new_cost[i] = T.costs[i];
        }

        // y connexions made
        std::array<unsigned char, n> min_branch, max_branch;
        for(int i=0; i<n; ++i){
            min_branch[i] = vertical_order[i];
            max_branch[i] = vertical_order[i];
        }
        // Greedily make them
        for(int i=0; i<n-1; ++i){
            // Either we make the vertical part of the connexion here (i.e. do nothing) or we report it restricted
            unsigned char f = T.sorted_nodes[i];
            unsigned char s = T.last_connexion[i];
            assert(min_branch[f] <= max_branch[f] and min_branch[s] <= max_branch[s]);
            min_branch[s] = std::min(max_branch[f], min_branch[s]);
            max_branch[s] = std::max(min_branch[f], max_branch[s]);
        }
        // Add them to the cost
        for(int i=n-1; i<2*n-2; ++i){
            new_cost[i] = 0;
        }
        for(int i=0; i<n; ++i){
            for(int j=min_branch[i]; j<max_branch[i]; ++j){
                new_cost[n-1 + j]++;
            }
        }

        // remove all dominated costs
        bool keep = true;
        for(int i=0; i<current_best_costs.size(); ++i){
            bool dominates=true, dominated=true;
            for(int j=0; j<2*n-2; ++j){
                dominates = dominates && (new_cost[j] <= current_best_costs[i].cost[j]);
            }
            for(int j=0; j<2*n-2; ++j){
                dominated = dominated && (new_cost[j] >= current_best_costs[i].cost[j]);
            }
            if(dominates && !dominated){ // Remove the current one, which is inefficient
                current_best_costs.erase(current_best_costs.begin() + i);
                --i;
            }
            else if(dominated){
                keep = false; // No need to keep this wirelength vector
                break;
            }
        }
        if(keep){
            tmp_lookup_cost new_elt;
            new_elt.cost = new_cost;
            new_elt.tree_index = ind;
            current_best_costs.push_back(new_elt);
        }
    }

    std::vector<lookup_struct<n> > ret;
    for(auto L : current_best_costs){
        /*
        // Cost debug
        for(unsigned char c : L.cost){
            std::cout << static_cast<int>(c);
        }
        std::cout << std::endl;
        */
        ret.push_back(L.to_struct());
    }
    return ret;
}

template<int n>
void generate_all_permutations(std::vector<std::array<unsigned char, n> > & permutations){
    static_assert(n >= 2, "Too small");
    std::array<unsigned char, n> sigma;
    for(int i=0; i<n; ++i){
        sigma[i] = i;
    }
    do{
        permutations.push_back(sigma);
    }while(std::next_permutation(sigma.begin(), sigma.end()));
}

template<int n>
void report_table(std::vector<std::vector<lookup_struct<n> > > const & POWVs, std::vector<fixed_size_tree<n> > const & f_x_trees){
    std::cout << "Total of " << POWVs.size() << " permutations" << std::endl;

    std::vector<bool> used(f_x_trees.size(), false);
    int tot_size = 0, max_size = 0;
    for(std::vector<lookup_struct<n> > const V : POWVs){
        tot_size += V.size();
        max_size = std::max(max_size, (int) V.size());
        for(auto L : V){
            used[L.tree_index] = true;
        }
    }
    int tot_used = 0;
    for(bool B : used){
        if(B){
            tot_used++;
        }
    }
    std::cout << "Mean size of lookup table is " << static_cast<float>(tot_size) / POWVs.size() << std::endl;
    std::cout << "Max size of lookup table is " << max_size << std::endl;
    std::cout << "A total of " << tot_used << " x_trees are used out of " << f_x_trees.size() << std::endl;
}

template<int n>
void write_human_readable_table(std::vector<std::vector<lookup_struct<n> > > POWVs, std::vector<std::array<unsigned char, n> > permutations){
    assert(POWVs.size() == permutations.size());

    for(int ind = 0; ind < permutations.size(); ++ind){
        for(auto s : permutations[ind]){
            std::cout << static_cast<int>(s);
        }
        std::cout << " : ";
        
        auto const V = POWVs[ind];
        std::cout << V.size() << "\n";
        for(auto const L : V){
            // x cost
            std::cout << "-";
            for(int i=0; i < n - 2; ++i){
                assert(not (L.cost[i] and L.cost[2*n-4 + i]));
                if(L.cost[i]){
                    std::cout << "+";
                }
                else if(L.cost[2*n-4 + i]){
                    std::cout << "-";
                }
                else{
                    std::cout << ".";
                }
            }
            std::cout << "+ -";
            // y cost
            for(int i=n-2; i < 2*n - 4; ++i){
                assert(not (L.cost[i] and L.cost[2*n-4 + i]));
                if(L.cost[i]){
                    std::cout << "+";
                }
                else if(L.cost[2*n-4 + i]){
                    std::cout << "-";
                }
                else{
                    std::cout << ".";
                }
            }
            std::cout << "+ " << L.tree_index;
            std::cout << "\n";
        }
        std::cout << std::endl;
    }
}

template<int n>
void write_standard_table(std::vector<std::vector<lookup_struct<n> > > table){
    std::cout << table.size() << std::endl;
    for(auto line : table){
        std::cout << line.size() << std::endl;
        for(auto POWV : line){
            std::cout << POWV.cost.to_ulong() << " : " << POWV.tree_index << std::endl;
        }
    }
}

template<int n>
std::vector<std::vector<lookup_struct<n> > > read_table(){

}

template<int n>
void write_tree_table(std::vector<fixed_size_tree<n> > f_trees){
    // Output final fixed trees
    std::cout << f_trees.size() << "\n";
    for(auto T : f_trees){
        for(unsigned char c : T.sorted_nodes){
            std::cout << static_cast<int>(c);
        }
        std::cout << " ";
        for(unsigned char c : T.last_connexion){
            std::cout << static_cast<int>(c);
        }
        std::cout << " : ";
        for(unsigned char c : T.prufer_representation){
            std::cout << static_cast<int>(c);
        }
        std::cout << "\n";
    }
}

template<int n>
std::vector<fixed_size_tree<n> > read_tree_table(){

}

std::vector<int> greedy_min_cover(std::vector<std::vector<int> > redundant_cover){
    
}

int main(){

    const int n = EXTERNAL_N;
    std::vector<tree> x_trees;

    if(n > 2){
        std::vector<int> prufers(n-2, n-1);
        generate_prufers(n, n-2, prufers, x_trees);
    }

    

    std::vector<fixed_size_tree<n> > f_x_trees;
    for(tree const T : x_trees){
        /*
        // Debug initial tree
        for(auto e : T.edges){
            std::cout << e.f << "," << e.s << " ";
        }
        std::cout << " : ";
        for(int i : T.prufer_representation){
            std::cout << i;
        }
        std::cout << std::endl;
        */
        f_x_trees.push_back(get_fixed<n>(T));
    }
    std::sort(f_x_trees.begin(), f_x_trees.end());
    

    
    // Iterate through all permutations to find their optimal trees
    
    std::vector<std::vector<lookup_struct<n> > > POWVs;
    std::vector<std::array<unsigned char, n> > permutations;
    generate_all_permutations<n>(permutations);
    for(auto sigma : permutations){
        POWVs.push_back(get_optimal_costs<n>(sigma, f_x_trees));
    }

    report_table(POWVs, f_x_trees);
    //write_standard_table(POWVs);
    //write_human_readable_table<n>(POWVs, permutations);
    

    return 0;
}
