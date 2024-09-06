use expander_rs::{Circuit,GKRConfig,CircuitLayer,GateAdd};
use halo2_solidity_verifier::revm::primitives::HashMap;
use powdr_number::FieldElement;
use std::{cmp::max, collections::BTreeMap, iter, sync::Arc};
use powdr_executor::witgen::WitgenCallback;

use powdr_ast::analyzed::{
    AlgebraicBinaryOperation, AlgebraicBinaryOperator, AlgebraicExpression, SelectedExpressions,
};
use powdr_ast::{
    analyzed::{Analyzed, IdentityKind},
    parsed::visitor::ExpressionVisitable,
};

use super::circuit_builder;
use super::prover::GkrProver;

struct GkrMapping<T>{
    data: HashMap<String,Vec<T>>,
    flattened: Vec<T>,
    column_offsets: HashMap<String, usize>,
    num_rows: usize,
}

impl<T: Clone> GkrMapping<T> {
    // Creates a new `GkrMapping` from a HashMap of column names to vectors
    pub fn new(data: HashMap<String, Vec<T>>) -> Self {
        let mut flattened = Vec::new();
        let mut column_offsets = HashMap::new();
        let mut current_offset = 0;

        // Determine the number of rows in the table
        let num_rows = data.values().next().map_or(0, |col| col.len());

        // Concatenate columns and calculate offsets
        for (column_name, column_data) in &data {
            column_offsets.insert(column_name.clone(), current_offset);
            flattened.extend_from_slice(column_data);
            current_offset += column_data.len();
        }

        GkrMapping {
            data,
            flattened,
            column_offsets,
            num_rows,
        }
    }
    pub fn index(&self, column_name: &str, row: usize) -> usize {
        assert!(
            row < self.num_rows,
            "Row index out of bounds: {} >= {}",
            row,
            self.num_rows
        );

        // Get the starting index of the column in the flattened vector
        let start_index = self
            .column_offsets
            .get(column_name)
            .expect("Column name not found in the table");

        // Calculate the position in the flattened vector
        start_index + row
    }
}


fn create_hashmap<T:Clone>(
    fixed: &[(String, Vec<T>)],
    witness: &[(String, Vec<T>)],
) -> HashMap<String, Vec<T>> {
    let mut map: HashMap<String, Vec<T>> = HashMap::new();

    // Insert all entries from `fixed` into the HashMap
    for (key, value) in fixed {
        map.insert(key.clone(), (*value).clone());
    }

    // Insert all entries from `witness` into the HashMap
    // If there are duplicate keys, values from `witness` will override `fixed`
    for (key, value) in witness {
        map.insert(key.clone(), (*value).clone());
    }

    map
}



pub fn convert_pil_to_gkr<T: FieldElement,C:GKRConfig>(pil: Arc<Analyzed<T>>,fixed: & [(String, Vec<T>)],witness: &[(String, Vec<T>)],
witgen_callback: WitgenCallback<T>)->Circuit<C>{
    let mut circuit=Circuit::<C>::default();

    println!("fixed length {}",fixed.len());
    println!("witness length {}",witness.len());


    for (fixed_name, values) in fixed.iter() {
        println!("Name: {}", fixed_name); // Print the String part

        // Print each element in the inner Vec<T>
        print!("Values: ");
        for value in values {
            print!("{} ", value);
        }
        println!(); // Newline for each tuple
    }

    for (fixed_name, values) in witness.iter() {
        println!("Name: {}", fixed_name); // Print the String part

        // Print each element in the inner Vec<T>
        print!("Values: ");
        for value in values {
            print!("{} ", value);
        }
        println!(); // Newline for each tuple
    }

    let allcolumns=create_hashmap(&fixed, &witness);
    let table=GkrMapping::new(allcolumns);

   

    println!("Degree: {}", pil.degree());
    println!(
        "Commitment count + Constant count: {}",
        pil.commitment_count() + pil.constant_count()
    );

    // set inputs number for gkr circuit
    let inputs_number: f64 = (pil.degree() as f64) * ((pil.commitment_count() + pil.constant_count()) as f64);
    
    let mut l0=CircuitLayer::<C>::default();
    l0.input_var_num=(inputs_number).log2().ceil() as usize;
    println!("input_var_num {:?}",l0.input_var_num);
    l0.output_var_num=l0.input_var_num;

    for i in 0.. (pil.degree()-1){
        l0.add.push(GateAdd{
            i_ids:[table.index("Fibonacci::ISLAST", 1)],
            o_id:(i as usize),
            coef:C::CircuitField::from(1 as u32),
            is_random:false,
            gate_type:1,
        });

        l0.add.push(GateAdd{
            i_ids:[table.index("Fibonacci::y", (i+1) as usize)],
            o_id:(i as usize),
            coef:C::CircuitField::from(1 as u32),
            is_random:false,
            gate_type:1,
        });
    }
    circuit.layers.push(l0.clone());

    
    

    circuit
}
