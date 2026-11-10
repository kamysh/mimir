//! Observe all reserved learning-item owners, including legacy rows without a local key.
use tokio_postgres::{Error, Transaction};
use uuid::Uuid;

#[derive(Debug, PartialEq)]
pub struct ItemOwner {
    pub identity: Uuid,
    pub experience: Uuid,
    pub source_ref: String,
    pub actor: String,
    pub item_key: Option<String>,
}

pub async fn observe(tx: &Transaction<'_>) -> Result<Vec<ItemOwner>, Error> {
    tx.query("SELECT item_id, experience_id, source_ref, actor, item_key FROM public.mimir_learning_item_owners ORDER BY item_id", &[])
        .await?.into_iter().map(|row| Ok(ItemOwner {
            identity: row.try_get(0)?, experience: row.try_get(1)?, source_ref: row.try_get(2)?,
            actor: row.try_get(3)?, item_key: row.try_get(4)?,
        })).collect()
}
