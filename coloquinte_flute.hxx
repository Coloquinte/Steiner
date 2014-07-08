/*
 * coloquinte_flute.hxx
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

template<typename T>
struct point{
    T x, y;
    point(T a, T b) : x(a), y(b){}
};

template<typename T>
struct labeled_point : public point<T>{
    int ind;
    labeled_point(T a, T b, int i) : point(a, b), ind(i){}
};

template<int n>
struct lookup_struct{
    // First the x entries (n-3 positive from 2 to n-1 then n-3 negative from 1 to n-2), then the y entries
    // On a Steiner trees, the first and last entries are not taken into account (always negative/always positive)
    // The second may not be positive, like the n-2 one cannot be negative, hence the n-3 entries
    std::bitset<4*n - 12> cost;

    // Could be vectorized quite easily on AVX
    template<typename T>
    T evaluate(std::array<T, 4*n-12> position_vector){
        std::array<T, 4*n-12> masked;
        for(int i=0; i < 4*n -12; ++i){
            masked[i] = (cost[i] ? position_vector[i] : 0);
        }
        return std::accumulate(masked.begin(), masked.end(), 0);
    }

    lookup_struct(){
        for(int i=0; i<4*n-12; ++i){
            cost[b] = false;
        }
    }

    // All of them assume everything is initialized to false
    void set_positive_x(int ind){
        assert(ind > 1);
        assert(ind < n-1);
        cost[ind - 2] = true;
    }
    void set_negative_x(int ind){
        assert(ind > 0);
        assert(ind < n-2);
        cost[n-3+ind-1] = true;
    }
    void set_positive_y(int ind){
        assert(ind > 1);
        assert(ind < n-1);
        cost[2*n-6+ind-2] = true;
    }
    void set_negative_y(int ind){
        assert(ind > 0);
        assert(ind < n-2);
        cost[3*n-9+ind-1] = true;
    }
};

// Dominates another POWV (non strict)
template<int n>
bool dominates(lookup_struct<n> const & a, lookup_struct<n> const & b) const{
    // Avoid code duplication between x and y
    auto evaluate = [&](int inpos)->bool{
        const int neg_offset = n-3;
        bool ret = true;
        // Cost of b on this edge - cost of a on this edge
        int active = 0;
        if(a.cost[inpos]){
            --active;
        }
        if(b.cost[inpos]){
            ++active;
        }
        ret = ret && active >= 0;
        for(int i=0; i<n-4; ++i){
            if(b.cost[inpos+i+1]){
                ++active;
            }
            if(a.cost[inpos+i+1]){
                --active;
            }
            if(b.cost[inpos+neg_offset+i]){
                --active;
            }
            if(a.cost[inpos+neg_offset+i]){
                ++active;
            }
            ret = ret && active >= 0;
        }
        if(b.cost[inpos+neg_offset+i]){
            --active;
        }
        if(a.cost[inpos+neg_offset+i]){
            ++active;
        }
        ret = ret && active >= 0;

        return ret;
    };
    return evaluate(0) and evaluate(2*n-6);
}

// Both arrays are in order
template<typename T, int n>
std::array<T, 4*n - 12> get_lookup_array(std::array<T, n> x_pos, std::array<T, n> y_pos){
    std::array<T, 4*n - 12> ret;
    for(int i=0; i<n-3; ++i){
        ret[       i] =  x_pos[i+1];
        ret[n-3   +i] = -x_pos[i+2];
    }
    for(int i=0; i<n-3; ++i){
        ret[2*n-6 +i] =  y_pos[i+1];
        ret[3*n-9 +i] = -y_pos[i+2];
    }
    return ret;
}

template<int n>
struct sorted_tree{
    static_assert(n >= 2, "A tree must have at least 2 vertices");

    std::array<unsigned char, 2*n-2> edges;

    // To prune obviously suboptimal Steiner trees and keep only one representant for equivalent ones if agressive is set to true
    bool is_kept(bool agressive = true) const{
        std::array<int, n> before, after;
        for(int i=0; i<n; ++i){ before[i] = 0; after[i] = 0; }

        for(int i=0; i<n-1; ++i){
            unsigned char f = edges[2*i], s = edges[2*i+1];
            assert(f != s);
            if(f < s){
                after[f]++; before[s]++;
            }
            else{
                after[s]++; before[f]++;
            }
        }
        bool feasible = true;
        for(int i=0; i<n; ++i){
            feasible = feasible and std::abs(after[i] - before[i]) <= 1 and (!agressive or before[i] <= after[i] or after[i] == 0); // If agressive, keep only one representant where the vertical edge is at the leftmost possible position
        }
        return feasible;
    }

    // Assumes the tree is at least potentially optimal
    lookup_struct<n> get_lookup_cost(std::array<int, n> permutation) const{
        lookup_struct<n> ret;
        for(bool & b : ret.cost){ b=false; }

        std::array<int, n> min_branch, max_branch;
        for(int i=0; i<n; ++i){
            min_branch[i] = permutation[i];
            max_branch[i] = permutation[i];
        }
        
        std::array<int, n> before, after;
        for(int i=0; i<n; ++i){ before[i] = 0; after[i] = 0; }

        for(int j=0; j<2*n-2; j+=2){
            // y cost
            // The edge is the current pair of uint8_t
            f = edges[j]; s = edges[j+1];
            max_branch[s] = std::max(min_branch[f], max_branch[s]);
            min_branch[s] = std::min(max_branch[f], min_branch[s]);

            // Set the cost in the lookup table
            if(min_branch[f] != 0 and min_branch[f] != n-1){
                ret.set_negative_y(min_branch[f]);
            }
            if(max_branch[f] != 0 and max_branch[f] != n-1){
                ret.set_positive_y(min_branch[f]);
            }


            // x cost
            unsigned char f = edges[j], s = edges[j+1+1];
            if(f < s){
                after[f]++; before[s]++;
            }
            else{
                after[s]++; before[f]++;
            }
        }

        // Final calculation of the x cost
        for(int i=1; i<n-1; ++i){
            if(after[i] < before[i]){
                ret.set_positive_x(i);
            }
            if(after[i] > before[i]){
                ret.set_negative_x(i);
            }
        }
        return ret;
    }

    // The x array is in sorted order, the y array in the corresponding order
    template<typename T>
    T get_cost(std::array<T, n> x_pos, std::array<T, n> y_pos) const{
        T cost = 0;
        std::array<T, n> min_branch, max_branch;
        for(int i=0; i<n; ++i){
            min_branch[i] = y_pos[i];
            max_branch[i] = y_pos[i];
        }
        int f,s;
        for(int j=0; j<2*n-2; j+=2){
            // The edge is the current pair of uint8_t
            f = edges[j]; s = edges[j+1];
            cost += (x_pos[s] - x_pos[f]);
            cost += (max_branch[f] - min_branch[f]);
            max_branch[s] = std::max(min_branch[f], max_branch[s]);
            min_branch[s] = std::min(max_branch[f], min_branch[s]);
        }
        cost += (max_branch[s] - min_branch[s]);
        return cost;
    }
};

// Various comparison functions; they change the outcome when selecting trees for cover
bool basic_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    return a.edges < b.edges;
}
bool first_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = a.edges[2*i];
        b_e[i] = b.edges[2*i];
    }
    return a_e < b_e;
}
bool prufer_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = a.edges[2*i+1];
        b_e[i] = b.edges[2*i+1];
    }
    return a_e < b_e;
}
bool smallest_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = std::min(a.edges[2*i], a.edges[2*i+1]);
        b_e[i] = std::min(b.edges[2*i], b.edges[2*i+1]);
    }
    return a_e < b_e;
}

bool operator<(sorted_tree<n> const a, sorted_tree<n> const b){
    return smallest_lexicographic(a, b);
}

