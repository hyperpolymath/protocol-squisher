// SPDX-License-Identifier: PMPL-1.0-or-later
// Test schema for CLI demonstration

use serde::{Deserialize, Serialize};

#[derive(Debug, Serialize, Deserialize)]
pub struct User {
    pub id: i64,
    pub name: String,
    pub email: String,
    pub age: i32,
    pub balance: f64,
}

#[derive(Debug, Serialize, Deserialize)]
pub struct Product {
    pub product_id: i64,
    pub title: String,
    pub price: f64,
    pub quantity: i32,
}

fn main() {
    let user = User {
        id: 1,
        name: "Alice".to_string(),
        email: "alice@example.com".to_string(),
        age: 30,
        balance: 1000.50,
    };
    let product = Product {
        product_id: 42,
        title: "Widget".to_string(),
        price: 9.99,
        quantity: 100,
    };
    println!("User: {:?}", user);
    println!("Product: {:?}", product);
    println!("Schema types available for CLI analysis.");
}
