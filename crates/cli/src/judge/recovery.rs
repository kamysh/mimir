use super::state::{Remedy, RepairCase};
use mimir_core::learning::ExperienceState;
use std::{collections::VecDeque, path::PathBuf, time::Duration};
use uuid::Uuid;

#[derive(Debug)]
pub(super) struct ProviderReset(pub Duration);

impl ProviderReset {
    pub fn from_header(value: &str) -> Option<Self> {
        if let Ok(seconds) = value.parse::<u64>() {
            return Some(Self(Duration::from_secs(seconds)));
        }
        let date = chrono::DateTime::parse_from_rfc2822(value).ok()?;
        Some(Self(
            (date.to_utc() - chrono::Utc::now())
                .to_std()
                .unwrap_or_default(),
        ))
    }
}

impl std::fmt::Display for ProviderReset {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "The provider requested a wait of {:?}", self.0)
    }
}
impl std::error::Error for ProviderReset {}

#[derive(Clone, Debug)]
pub(super) enum Next {
    Scan,
    WorkEvent,
    Lock(PathBuf),
    Reconnect,
    Provider(Duration),
    Correct { code: &'static str, action: String },
}

#[derive(Clone, Debug)]
pub(super) enum Obstacle {
    Model(String, Option<Duration>),
    Tool(String),
    NoSubmission(String),
    Decision(RepairCase),
}

#[derive(Clone, Debug)]
pub(super) enum Task {
    Prepare,
    VerifySource,
    VerifyOutcome(Obstacle),
}

pub(super) enum Resolution {
    Requeue(Entry),
    Shared(Next),
    Repair(RepairCase),
}

impl Obstacle {
    pub fn after_pending_read(self, mut entry: Entry) -> Resolution {
        let case = match self {
            Self::Decision(case) => case,
            Self::Model(_, Some(delay)) => return Resolution::Shared(Next::Provider(delay)),
            _ if !entry.fresh => {
                entry.fresh = true;
                entry.task = Task::Prepare;
                return Resolution::Requeue(entry);
            }
            Self::Model(detail, None) => RepairCase::new(Remedy::ChooseBackend,
                "The judge stopped on a fresh attempt. Choose a working backend or restore its account.", detail),
            Self::Tool(detail) => RepairCase::new(Remedy::RestoreClient,
                "The review tool failed on a fresh attempt. Restore it or select a compatible MCP server.", detail),
            Self::NoSubmission(detail) => RepairCase::new(Remedy::EditReview,
                "The judge finished a fresh attempt without submitting a review. Supply or correct the review.", detail),
        };
        Resolution::Repair(case)
    }
}

#[derive(Clone, Debug)]
pub(super) struct Entry {
    pub id: Uuid,
    pub revision: i64,
    pub prior_review: i64,
    pub project: String,
    pub fresh: bool,
    pub task: Task,
}

impl Entry {
    pub fn first(state: &ExperienceState) -> Self {
        Self {
            id: state.experience.id,
            revision: state.revision,
            prior_review: state.review_revision,
            project: state.experience.project.clone(),
            fresh: false,
            task: Task::Prepare,
        }
    }

    pub fn pending(&self, row: &ExperienceState) -> bool {
        row.experience.id == self.id
            && row.experience.project == self.project
            && row.revision == self.revision
            && row.review_revision == self.prior_review
            && row.reviewed_revision < self.revision
    }
}

#[derive(Default)]
pub(super) struct Session {
    pub transcripts: super::transcript::Pending,
    pub ready: VecDeque<Entry>,
    scope: Option<(String, u16, String, String, Option<String>)>,
}

impl Session {
    pub fn select_scope(&mut self, settings: &super::config::RuntimeConfig) {
        let db = &settings.core.database;
        let scope = (
            db.host.clone(),
            db.port,
            db.dbname.clone(),
            db.user.clone(),
            settings.judge.project.clone(),
        );
        if self.scope.as_ref() != Some(&scope) {
            self.ready.clear();
            self.scope = Some(scope);
        }
    }
}
