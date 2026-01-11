// SPDX-License-Identifier: PMPL-1.0
// SPDX-FileCopyrightText: 2025 hyperpolymath

//! Example schema for testing protocol-squisher

use serde::{Deserialize, Serialize};

/// A user in the system
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: i64,
    pub name: String,
    pub email: Option<String>,
    pub role: Role,
    pub tags: Vec<String>,
}

/// User role enumeration
#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Role {
    Admin,
    User,
    Guest,
}

/// An order in the system
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: i64,
    pub user_id: i64,
    pub items: Vec<OrderItem>,
    pub status: OrderStatus,
    pub total: f64,
}

/// An item in an order
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: i64,
    pub quantity: u32,
    pub price: f64,
}

/// Order status with associated data
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", content = "data")]
pub enum OrderStatus {
    Pending,
    Processing(String),
    Shipped { tracking: String, carrier: String },
    Delivered,
    Cancelled(String),
}
