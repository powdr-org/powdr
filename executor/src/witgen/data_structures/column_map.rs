use std::{
    marker::PhantomData,
    ops::{Index, IndexMut},
};

use powdr_ast::analyzed::{PolyID, PolynomialType};

// Marker types for each PolynomialType
#[derive(Debug, Clone, Copy)]
pub struct Witness;

#[derive(Debug, Clone, Copy)]
pub struct Fixed;

pub trait PolynomialTypeTrait {
    const P_TYPE: PolynomialType;
}

impl PolynomialTypeTrait for Witness {
    const P_TYPE: PolynomialType = PolynomialType::Committed;
}

impl PolynomialTypeTrait for Fixed {
    const P_TYPE: PolynomialType = PolynomialType::Constant;
}

pub type WitnessColumnMap<V> = ColumnMap<V, Witness>;
pub type FixedColumnMap<V> = ColumnMap<V, Fixed>;

/// A Map indexed by polynomial ID, for a specific polynomial type (e.g. fixed or witness).
/// For performance reasons, it uses a Vec<V> internally and assumes that the polynomial IDs
/// are contiguous.
#[derive(Debug, Clone)]
pub struct ColumnMap<V, T: PolynomialTypeTrait> {
    values: Vec<V>,
    _ptype: PhantomData<T>,
}

impl<V: Clone, T: PolynomialTypeTrait> ColumnMap<V, T> {
    /// Create a new ColumnMap with the given initial value and size.
    pub fn new(initial_value: V, size: usize) -> Self {
        ColumnMap {
            values: vec![initial_value; size],
            _ptype: PhantomData,
        }
    }
}

impl<V, T: PolynomialTypeTrait> ColumnMap<V, T> {
    pub fn from(values: impl Iterator<Item = V>) -> Self {
        ColumnMap {
            values: values.collect(),
            _ptype: PhantomData,
        }
    }

    /// Creates a ColumnMap from an iterator over PolyIDs and values.
    pub fn from_indexed(items: impl Iterator<Item = (PolyID, V)>, len: usize) -> Self
    where
        V: Default,
    {
        let mut values: Vec<V> = (0..len).map(|_| V::default()).collect();
        for (poly, value) in items {
            values[poly.id as usize] = value;
            debug_assert_eq!(poly.ptype, T::P_TYPE);
        }

        ColumnMap {
            values,
            _ptype: PhantomData,
        }
    }

    pub fn keys(&self) -> impl Iterator<Item = PolyID> {
        (0..self.values.len()).map(move |i| PolyID {
            id: i as u64,
            ptype: T::P_TYPE,
        })
    }

    pub fn iter(&self) -> impl Iterator<Item = (PolyID, &V)> {
        self.keys().zip(self.values.iter())
    }

    pub fn into_iter(self) -> impl Iterator<Item = (PolyID, V)> {
        self.keys().zip(self.values)
    }

    pub fn values(&self) -> impl Iterator<Item = &V> {
        self.values.iter()
    }

    pub fn values_into_iter(self) -> impl Iterator<Item = V> {
        self.values.into_iter()
    }

    pub fn values_iter_mut(&mut self) -> impl Iterator<Item = &mut V> {
        self.values.iter_mut()
    }

    pub fn len(&self) -> usize {
        self.values.len()
    }
}

impl<V, T: PolynomialTypeTrait> Default for ColumnMap<V, T> {
    fn default() -> Self {
        ColumnMap {
            values: Vec::new(),
            _ptype: PhantomData,
        }
    }
}

impl<V: PartialEq, T: PolynomialTypeTrait> PartialEq for ColumnMap<V, T> {
    fn eq(&self, other: &Self) -> bool {
        self.values == other.values
    }
}

impl<V, T: PolynomialTypeTrait> Index<&PolyID> for ColumnMap<V, T> {
    type Output = V;

    #[inline]
    fn index(&self, poly_id: &PolyID) -> &Self::Output {
        debug_assert!(poly_id.ptype == T::P_TYPE);
        &self.values[poly_id.id as usize]
    }
}

impl<V, T: PolynomialTypeTrait> IndexMut<&PolyID> for ColumnMap<V, T> {
    #[inline]
    fn index_mut(&mut self, poly_id: &PolyID) -> &mut Self::Output {
        debug_assert!(poly_id.ptype == T::P_TYPE);
        &mut self.values[poly_id.id as usize]
    }
}
