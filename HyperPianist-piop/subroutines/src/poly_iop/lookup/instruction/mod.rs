use enum_dispatch::enum_dispatch;
use fixedbitset::*;
use rand::prelude::StdRng;
use serde::Serialize;
use std::marker::Sync;
use std::ops::Range;

use ark_ff::PrimeField;
use super::subtable::LassoSubtable;

mod util;

use util::chunk_operand;
pub use util::evaluate_mle_dechunk_operands;
pub use util::concatenate_lookups;

use std::fmt::Debug;

#[enum_dispatch]
pub trait JoltInstruction: Clone + Debug + Send + Sync + Serialize {
    fn operands(&self) -> (u64, u64);
    /// Combines `vals` according to the instruction's "collation" polynomial `g`.
    /// If `vals` are subtable entries (as opposed to MLE evaluations), this function returns the
    /// output of the instruction. This function can also be thought of as the low-degree extension
    /// for the instruction.
    ///
    /// Params:
    /// - `vals`: Subtable entries or MLE evaluations. Assumed to be ordered
    ///           [T1_1, ..., T1_C, T2_1, ..., T2_C, ..., Tk_1, ..., Tk_C]
    ///           where T1, ..., Tk are the unique subtable types used by this instruction, in the order
    ///           given by the `subtables` method below. Note that some subtable values may be unused.
    /// - `C`: The "dimension" of the decomposition, i.e. the number of values read from each subtable.
    /// - `M`: The size of each subtable/memory.
    ///
    /// Returns: The combined value g(vals).
    fn combine_lookups<F: PrimeField>(&self, vals: &[F], C: usize, M: usize) -> F;
    /// The degree of the `g` polynomial described by `combine_lookups`
    fn g_poly_degree(&self, C: usize) -> usize;
    /// Returns a Vec of the unique subtable types used by this instruction. For some instructions,
    /// e.g. SLL, the list of subtables depends on the dimension `C`.
    fn subtables<F: PrimeField>(
        &self,
        C: usize,
        M: usize,
    ) -> Vec<(Box<dyn LassoSubtable<F>>, SubtableIndices)>;
    /// Converts the instruction operand(s) in their native word-sized representation into a Vec
    /// of subtable lookups indices. The returned Vec is length `C`, with elements in [0, `log_M`).
    fn to_indices(&self, C: usize, log_M: usize) -> Vec<usize>;
    /// Computes the output lookup entry for this instruction as a u64.
    fn lookup_entry(&self) -> u64;
    fn operand_chunks(&self, C: usize, log_M: usize) -> (Vec<u64>, Vec<u64>) {
        assert!(
            log_M % 2 == 0,
            "log_M must be even for operand_chunks to work"
        );
        let (left_operand, right_operand) = self.operands();
        (
            chunk_operand(left_operand, C, log_M / 2),
            chunk_operand(right_operand, C, log_M / 2),
        )
    }
    fn random(&self, rng: &mut StdRng) -> Self;

    fn slice_values<'a, F: PrimeField>(&self, vals: &'a [F], C: usize, M: usize) -> Vec<&'a [F]> {
        let mut offset = 0;
        let mut slices = vec![];
        for (_, indices) in self.subtables::<F>(C, M) {
            slices.push(&vals[offset..offset + indices.len()]);
            offset += indices.len();
        }
        assert_eq!(offset, vals.len());
        slices
    }
}

#[derive(Clone)]
pub struct SubtableIndices {
    bitset: FixedBitSet,
}

impl SubtableIndices {
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            bitset: FixedBitSet::with_capacity(capacity),
        }
    }

    pub fn union_with(&mut self, other: &Self) {
        self.bitset.union_with(&other.bitset);
    }

    pub fn iter(&self) -> impl Iterator<Item = usize> + '_ {
        self.bitset.ones()
    }

    #[allow(clippy::len_without_is_empty)]
    pub fn len(&self) -> usize {
        self.bitset.count_ones(..)
    }

    pub fn contains(&self, index: usize) -> bool {
        self.bitset.contains(index)
    }
}

impl From<usize> for SubtableIndices {
    fn from(index: usize) -> Self {
        let mut bitset = FixedBitSet::new();
        bitset.grow_and_insert(index);
        Self { bitset }
    }
}

impl From<Range<usize>> for SubtableIndices {
    fn from(range: Range<usize>) -> Self {
        let bitset = FixedBitSet::from_iter(range);
        Self { bitset }
    }
}

pub mod and;
pub mod or;
pub mod xor;

#[cfg(test)]
pub mod test;
