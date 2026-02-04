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
