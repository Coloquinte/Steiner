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
#include <string>

template<typename T>
struct point{
    T x, y;
    point(T a, T b) : x(a), y(b){}
};

template<typename T>
struct labeled_point : public point<T>{
    int ind;
    labeled_point(T a, T b, int i) : point<T>(a, b), ind(i){}
};

template<int n>
struct lookup_cost{
    std::array<unsigned char, n-1> x_cost, y_cost;

    lookup_cost(){
        for(unsigned char & c : x_cost){
            c=0;
        }
        for(unsigned char & c : y_cost){
            c=0;
        }
    }

    bool operator<(lookup_cost<n> const o) const{
        return x_cost < o.x_cost || (x_cost == o.x_cost && y_cost < o.y_cost);
    }

    std::string to_string() const{
        std::string ret;
        for(unsigned char const c : x_cost){
            ret += std::to_string(static_cast<int>(c));
        }
        ret += "  "; // Two spaces to align with lookup_struct
        for(unsigned char const c : y_cost){
            ret += std::to_string(static_cast<int>(c));
        }
        return ret;
    }
};

// Dominates another POWV (non strict)
template<int n>
bool dominates(lookup_cost<n> const & a, lookup_cost<n> const & b){
    bool ret = true;
    for(int i=0; i<n-1; ++i){
        ret = ret && (a.x_cost[i] <= b.x_cost[i]);
    }
    for(int i=0; i<n-1; ++i){
        ret = ret && (a.y_cost[i] <= b.y_cost[i]);
    }
    return ret;
}

template<int n>
struct lookup_struct{
    // First the x entries (n-3 positive from 2 to n-1 then n-3 negative from 1 to n-2), then the y entries
    // On a Steiner trees, the first and last entries are not taken into account (always negative/always positive)
    // The second may not be positive, like the n-2 one cannot be negative, hence the n-3 entries
    std::bitset<4*n - 12> cost;

    bool operator<(lookup_struct<n> const o) const{
        return cost.to_ulong() < o.cost.to_ulong();
    }

    // Could be vectorized quite easily on AVX
    template<typename T>
    T evaluate(std::array<T, 4*n-12> position_vector){
        std::array<T, 4*n-12> masked;
        for(int i=0; i < 4*n -12; ++i){
            masked[i] = (cost[i] ? position_vector[i] : 0);
        }
        return std::accumulate(masked.begin(), masked.end(), 0);
    }

    lookup_struct(lookup_cost<n> const & o){
        for(int i=0; i<n-3; ++i){
            cost[      i] = (o.x_cost[i+1] > o.x_cost[i+2]); // Diminution of cost => positive contribution
        }
        for(int i=0; i<n-3; ++i){
            cost[  n-3+i] = (o.x_cost[i] < o.x_cost[i+1]); // Augmentation of cost => negative contribution
        }
        for(int i=0; i<n-3; ++i){
            cost[2*n-6+i] = (o.y_cost[i+1] > o.y_cost[i+2]); // Diminution of cost => positive contribution
        }
        for(int i=0; i<n-3; ++i){
            cost[3*n-9+i] = (o.y_cost[i] < o.y_cost[i+1]); // Augmentation of cost => negative contribution
        }
    }

    std::string to_string() const{
        const int neg_offset = n-3;

        std::string ret;
        // x output
        ret += "-";
        if(cost[neg_offset]){
            ret += "-";
        }
        else{
            ret += ".";
        }
        for(int i=0; i<n-4; ++i){
            if(cost[i]){
                ret += "+";
            }
            else if(cost[neg_offset+i+1]){
                ret += "-";
            }
            else{
                ret += ".";
            }
        }
        if(cost[n-4]){
            ret += "+";
        }
        else{
            ret += ".";
        }
        
        ret += "+ -";
 
        // y output
        if(cost[2*n-6+neg_offset]){
            ret += "-";
        }
        else{
            ret += ".";
        }
        for(int i=0; i<n-4; ++i){
            if(cost[2*n-6+i]){
                ret += "+";
            }
            else if(cost[2*n-6+neg_offset+i+1]){
                ret += "-";
            }
            else{
                ret += ".";
            }
        }
        if(cost[2*n-6+n-4]){
            ret += "+";
        }
        else{
            ret += ".";
        }
        ret += "+";

        return ret;
    }
};

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
    lookup_cost<n> get_lookup_cost(std::array<int, n> permutation) const{
        // Default-initialized to false
        lookup_cost<n> ret;

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
            unsigned char f = edges[j], s = edges[j+1];
            max_branch[s] = std::max(min_branch[f], max_branch[s]);
            min_branch[s] = std::min(max_branch[f], min_branch[s]);

            // x cost
            if(f < s){
                after[f]++; before[s]++;
            }
            else{
                after[s]++; before[f]++;
            }
        }

        int cur_x_cost = 0;
        // Final calculation of the x cost
        for(int i=0; i<n-1; ++i){
            assert(std::abs(after[i] - before[i]) <= 1); // Correctly pruned tree set
            if(after[i] < before[i]){
                --cur_x_cost;
            }
            if(after[i] > before[i]){
                ++cur_x_cost;
            }
            ret.x_cost[i] = static_cast<unsigned char>(cur_x_cost);
        }

        // Final calculation of the y cost
        std::array<int, n> relative_cost;
        for(int i=0; i<n; ++i){
            relative_cost[i] = 0;
        }
        for(int i=0; i<n; ++i){
            --relative_cost[max_branch[i]];
            ++relative_cost[min_branch[i]];
        }
        
        int cur_y_cost = 0;
        for(int i=0; i<n-1; ++i){
            assert(std::abs(relative_cost[i]) <= 1);
            cur_y_cost += relative_cost[i];
            ret.y_cost[i] = static_cast<unsigned char>(cur_y_cost);
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
template<int n>
bool basic_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    return a.edges < b.edges;
}
template<int n>
bool first_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, 2*n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i]   = a.edges[2*i];
        a_e[n+i] = a.edges[2*i+1];
        b_e[i]   = b.edges[2*i];
        b_e[n+i] = b.edges[2*i+1];
    }
    return a_e < b_e;
}
template<int n>
bool prufer_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = a.edges[2*i+1];
        b_e[i] = b.edges[2*i+1];
    }
    return a_e < b_e;
}
template<int n>
bool smallest_lexicographic(sorted_tree<n> const a, sorted_tree<n> const b){
    std::array<unsigned char, n> a_e, b_e;
    for(int i=0; i<n; ++i){
        a_e[i] = std::min(a.edges[2*i], a.edges[2*i+1]);
        b_e[i] = std::min(b.edges[2*i], b.edges[2*i+1]);
    }
    return a_e < b_e;
}

template<int n>
bool operator<(sorted_tree<n> const a, sorted_tree<n> const b){
    return first_lexicographic(a, b);
}

