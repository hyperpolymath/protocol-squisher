// Example Rust schema v2 - with some differences from v1
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: i64,
    pub name: String,
    // email is now required (not Optional)
    pub email: String,
    pub role: Role,
    // New field
    pub created_at: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Role {
    Admin,
    User,
    Guest,
    // New role
    Moderator,
}

// Order has different types
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: i64,
    pub user_id: i64,
    pub items: Vec<OrderItem>,
    // Changed from f64 to i32 (precision loss!)
    pub total: i32,
    pub status: OrderStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: i64,
    pub name: String,
    // Changed from u32 to i64 (widening)
    pub quantity: i64,
    pub price: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum OrderStatus {
    Pending,
    Processing,
    Shipped { tracking_number: String },
    Delivered { delivered_at: String },
    // Removed: Cancelled
}
