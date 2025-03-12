#![allow(dead_code)]
#![allow(unused_variables)]
#![allow(non_snake_case)]

use core::fmt;
use std::{borrow::Borrow, ops::{Add, Index, IndexMut, Sub}};

use fxhash::FxHashMap;
use itertools::Itertools;

#[derive(Debug)]
pub struct SetFunc {
    values:FxHashMap<Vec<u32>, i32>
}

impl SetFunc {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn subfunc<'a, I>(&self, Q:I) -> SmallSetFunc 
        where I: IntoIterator<Item=&'a u32> 
    {
        let Q = Q.into_iter().cloned().collect_vec();
        let mut res = SmallSetFunc::new(&Q);
        for subset in Q.into_iter().powerset() {
            if let Some(value) = self.values.get(&subset) {
                if *value != 0 {
                    res[&subset] = *value;
                }
            }
        }
        res
    }

    pub fn entries_nonzero(&self) -> impl Iterator<Item=(&Vec<u32>, i32)> + '_ {
        let res = self.values.iter()
            .filter(|(_, value)| **value != 0)
            .map(|(set,value)| (set, *value) );
        res
    }

    pub fn keys_nonzero(&self) -> impl Iterator<Item=&Vec<u32>> + '_ {
        let res = self.values.iter()
            .filter(|(_, value)| **value != 0)
            .map(|(set,_)| set );
        res
    }       
}

impl Default for SetFunc {
    fn default() -> Self {
        Self { values: FxHashMap::default() }
    }
}

// impl<'a, I> Index<I> for SetFunc where I: IntoIterator<Item=&'a u32> {
//     type Output = i32;

//     fn index(&self, query: I) -> &Self::Output {
//         let mut set:Vec<u32> = query.into_iter().cloned().collect();
//         set.sort_unstable();
//         set.dedup();

//         if self.values.contains_key(&set) {
//             &self.values[&set]
//         } else {
//             &0
//         }
//     }
// }

impl<I, V> Index<I> for SetFunc where V: Borrow<u32>, I: IntoIterator<Item=V> {
    type Output = i32;

    fn index(&self, query: I) -> &Self::Output {
        let mut set:Vec<u32> = query.into_iter().map(|u| *u.borrow()).collect();
        set.sort_unstable();
        set.dedup();

        if self.values.contains_key(&set) {
            &self.values[&set]
        } else {
            &0
        }
    }
}

impl<'a, I> IndexMut<I> for SetFunc where I: IntoIterator<Item=&'a u32> {
    fn index_mut(&mut self, query: I) -> &mut Self::Output {
        let mut set:Vec<u32> = query.into_iter().cloned().collect();
        set.sort_unstable();
        set.dedup();
        self.values.entry(set).or_default()
    }
}


#[derive(Debug,Clone)]
pub struct SmallSetFunc {
    universe:Vec<u32>,
    index_map:FxHashMap<u32, u8>,
    values:FxHashMap<u128, i32>    
}

impl SmallSetFunc {
    pub fn new<'a, I: IntoIterator<Item=&'a u32>>(universe:I) -> Self {
        let mut universe:Vec<u32> = universe.into_iter().cloned().collect();
        universe.sort_unstable();
        universe.dedup();

        Self::from_sorted_vec(universe)
    }

    pub fn size(&self) -> usize {
        self.universe.len()
    }

    fn from_sorted_vec(universe:Vec<u32>) -> Self {
        let index_map = universe.iter().enumerate().map(|(i,v)| (*v, i as u8) ).collect();
        let values = FxHashMap::default();

        SmallSetFunc{ universe, index_map, values }
    }

    fn convert_set<'a, I: IntoIterator<Item=&'a u32>>(&self, set:I) -> u128 {
        let mut res = 0u128;
        for x in set.into_iter() {
            let ix = self.index_map[x];
            assert!(ix < 128);
            res |= 1 << ix;
        }
        res
    }

    fn convert_bitset(&self, bitset:u128) -> Vec<u32> {
        let mut bitset = bitset;
        let mut res:Vec<u32> = Vec::default();
        while bitset != 0 {
            let ix = u128::trailing_zeros(bitset);
            bitset ^= 1 << ix;
            res.push(self.universe[ix as usize]);
        }

        res
    }

    pub fn mobius_trans_down(&mut self) {
        let n = self.size();
        
        for ix in 0..n {
            // Find all sets which do _not_ contain element w/ index ix 
            let ix_bit = 1 << ix;
            let active = self.values.keys().filter(|bitset| (**bitset & ix_bit) == 0).cloned().collect_vec();

            for target in active {
                let source = target | ix_bit; 
                let val = *self.values.get(&source).unwrap_or(&0);

                *self.values.entry(target).or_insert(0) -= val; // .and_modify(|e| *e = *e - val);
            }
        }
    }

    pub fn entries_nonzero(&self) -> impl Iterator<Item=(Vec<u32>, i32)> + '_ {
        let res = self.values.iter()
            .filter(|(bitset, value)| **value != 0)
            .map(|(bitset,value)| (self.convert_bitset(*bitset), *value) );
        res
    }

    pub fn keys_nonzero(&self) -> impl Iterator<Item=Vec<u32>> + '_ {
        let res = self.values.iter()
            .filter(|(_, value)| **value != 0)
            .map(|(bitset,_)| (self.convert_bitset(*bitset)) );
        res
    }   

    pub fn values_nonzero(&self) -> impl Iterator<Item=i32> + '_ {
        let res = self.values.values().cloned().filter(|value| *value != 0);
        res
    }

    pub fn count_nonzero(&self) -> usize {
        self.values.iter().filter(|(_, value)| **value != 0).count()
    } 

    pub fn contains_crown(&self) -> bool {
        if self.size() == 0 {
            return true;
        }

        let universe = (1 << self.size()) - 1;        
        let mut it = universe;
        while it != 0 { // Iterates over all ones in `universe`
            let ix = u128::trailing_zeros(it);
            let singleton = 1 << ix;
            it ^= singleton;
            let bitset = universe & !singleton;
            if self.is_zero(&bitset) {
                return false
            }
        }
        return true
    }

    pub fn contains_biclique(&self) -> bool {
        if self.size() == 0 {
            return true;
        }

        let universe = (1 << self.size()) - 1;
        self.is_at_least(&universe, &(self.size() as i32))
    }    

    pub fn is_ladder(&self) -> bool {
        if self.size() == 0 {
            return true;
        }

        if self.count_nonzero() < self.size() {
            return false;
        }

        let universe = (1 << self.size()) - 1;
        debug_assert_eq!(universe, self.convert_set(&self.universe));

        self.is_ladder_rec(universe, self.size())
    }
    
    fn is_ladder_rec(&self, bitset:u128, size:usize) -> bool {
        if size == 1 {
            return self.is_nonzero(&bitset);
        }

        if !self.values.contains_key(&bitset) {
            return false
        }

        let mut it = bitset;
        while it != 0 { // Iterates over all ones in `bitset`
            let ix = u128::trailing_zeros(it);
            it ^= 1 << ix;
            if self.is_ladder_rec(bitset & !(1 << ix), size-1) {
                return true
            }
        }   
        return false
    }

    #[inline]
    fn is_nonzero(&self, bitset:&u128) -> bool {
        self.values.get(bitset).map_or(false, |count| count > &0)
    }

    #[inline]
    fn is_at_least(&self, bitset:&u128, value:&i32) -> bool {
        self.values.get(bitset).map_or(false, |count| count >= value)
    }

    #[inline]
    fn is_zero(&self, bitset:&u128) -> bool {
        self.values.get(bitset).map_or(true, |count| count == &0)
    }    
}

impl<'a, I> Index<I> for SmallSetFunc where I: IntoIterator<Item=&'a u32> {
    type Output = i32;

    fn index(&self, query: I) -> &Self::Output {
        let bitset = self.convert_set(query);
        if self.values.contains_key(&bitset) {
            &self.values[&bitset]
        } else {
            &0
        }
    }
}

impl<'a, I> IndexMut<I> for SmallSetFunc where I: IntoIterator<Item=&'a u32> {
    fn index_mut(&mut self, query: I) -> &mut Self::Output {
        let bitset = self.convert_set(query);
        self.values.entry(bitset).or_default()
    }
}

impl Add<SmallSetFunc> for SmallSetFunc {
    type Output = SmallSetFunc;

    fn add(self, rhs: SmallSetFunc) -> Self::Output {
        assert_eq!(self.universe, rhs.universe);
        // Since both functions have the same universe, they also have the same
        // bitset representations.         

        let mut res = SmallSetFunc::from_sorted_vec(self.universe.clone());
        for (bitset, value) in self.values.iter().chain(rhs.values.iter()) {
            *res.values.entry(*bitset).or_default() += value;            
        }

        res
    }
}

impl Sub<SmallSetFunc> for SmallSetFunc {
    type Output = SmallSetFunc;

    fn sub(self, rhs: SmallSetFunc) -> Self::Output {
        assert_eq!(self.universe, rhs.universe);
        // Since both functions have the same universe, they also have the same
        // bitset representations.         

        let mut res = SmallSetFunc::from_sorted_vec(self.universe.clone());
        res.values = self.values;
        for (bitset, value) in rhs.values.iter() {
            *res.values.entry(*bitset).or_default() -= value;            
        }

        res
    }
}

impl fmt::Display for SmallSetFunc {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&format!("U={:?} ", self.universe))?;
        f.write_str("{")?;
        for (set, value) in self.entries_nonzero() {
            f.write_str(&format!("{set:?}: {value},"))?;
        }

        f.write_str("}")?;
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use crate::vecset::{difference, union};

    use super::*;

    #[test]
    fn test_inversion_2() {
        println!("-----------------------------");
        let mut R:SetFunc = SetFunc::new();
        R[&vec![]] = 751;
        R[&vec![0]] = 25;
        R[&vec![1]] = 133;
        R[&vec![0,1]] = 235;

        let f:SmallSetFunc = R.subfunc(&vec![0,1]);
        let mut F:SmallSetFunc = f.clone();

        for X in vec![0u32,1].into_iter().powerset() {
            assert_eq!(R[&X], f[&X]);
            assert_eq!(f[&X], F[&X]);
        }

        F.mobius_trans_down();

        println!("f = {f}");
        println!("F = {F}");

        let S = vec![0u32,1];
        let mut FF = SmallSetFunc::new(&S);
        for X in vec![0u32,1].into_iter().powerset() {
            let S_minus_X:Vec<_> = difference(&S, &X);
            let mut res:i32 = 0;

            for Y in S_minus_X.into_iter().powerset() {
                let k = Y.len();
                let Y = union(&X, &Y);

                if k % 2 == 0 {
                    res += R[&Y];
                } else {
                    res -= R[&Y];
                }
            }
            FF[&X] = res;
        }

        println!("FF = {FF}");
        for X in vec![0u32,1].into_iter().powerset() {
            assert_eq!(F[&X], FF[&X]);
        }
        println!("-----------------------------");
    }    

    #[test]
    fn test_inversion_3() {
        println!("-----------------------------");
        let mut R:SetFunc = SetFunc::new();
        R[&vec![]] = 751;
        R[&vec![0]] = 25;
        R[&vec![1]] = 133;
        R[&vec![2]] = 125;
        R[&vec![0,1]] = 235;
        R[&vec![0,2]] = 325;
        R[&vec![1,2]] = 124;
        R[&vec![0,1,2]] = 35;

        let f:SmallSetFunc = R.subfunc(&vec![0,1,2]);
        let mut F:SmallSetFunc = f.clone();

        for X in vec![0u32,1,2].into_iter().powerset() {
            assert_eq!(R[&X], f[&X]);
            assert_eq!(f[&X], F[&X]);
        }

        F.mobius_trans_down();

        println!("f = {f}");
        println!("F = {F}");

        let S = vec![0u32,1,2];
        let mut FF = SmallSetFunc::new(&S);
        for X in vec![0u32,1,2].into_iter().powerset() {
            let S_minus_X:Vec<_> = difference(&S, &X);
            let mut res:i32 = 0;

            for Y in S_minus_X.into_iter().powerset() {
                let k = Y.len();
                let Y = union(&X, &Y);

                if k % 2 == 0 {
                    res += R[&Y];
                } else {
                    res -= R[&Y];
                }
            }
            FF[&X] = res;
        }

        println!("FF = {FF}");
        for X in vec![0u32,1,2].into_iter().powerset() {
            assert_eq!(F[&X], FF[&X]);
        }
        println!("-----------------------------");
    }

    #[test]
    fn test_ladder() {
        let mut f:SmallSetFunc = SmallSetFunc::new(&vec![0,1,2,3]);

        assert!(!f.is_ladder());
        f[&vec![0,1,2,3]] = 1230;
        f[&vec![  1,2,3]] = 24;
        f[&vec![    2,3]] = 13;
        f[&vec![      3]] = 1231;
        assert!(f.is_ladder());
        f[&vec![      3]] = 0;
        assert!(!f.is_ladder());
        f[&vec![      2]] = 1;
        assert!(f.is_ladder());        
    }
}