// Example Rust schema for testing protocol-squisher
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct User {
    pub id: i64,
    pub name: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub email: Option<String>,
    pub role: Role,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub enum Role {
    Admin,
    User,
    Guest,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Order {
    pub id: i64,
    pub user_id: i64,
    pub items: Vec<OrderItem>,
    pub total: f64,
    pub status: OrderStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct OrderItem {
    pub product_id: i64,
    pub name: String,
    pub quantity: u32,
    pub price: f64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type")]
pub enum OrderStatus {
    Pending,
    Processing,
    Shipped { tracking_number: String },
    Delivered { delivered_at: String },
    Cancelled { reason: String },
}
