//! The sync→async bridge (the iamb `worker.rs` shape).
//!
//! `matrix-rust-sdk` is tokio-async; dregg's embedded executor is sync. The
//! confined comms-PD that hosts this client cannot block on a future directly —
//! it must hand work to a worker owning the tokio runtime and get a value back
//! over a channel. This module is the minimal, REAL version of that bridge:
//!
//! - [`MatrixWorker::spawn`] starts a multi-thread tokio runtime on its own OS
//!   thread, builds nothing yet, and listens for [`WorkerRequest`]s.
//! - [`MatrixHandle`] is the synchronous facade: each call sends a request plus a
//!   oneshot reply channel and blocks on the reply. This is exactly the
//!   request/response discipline iamb uses (`Requester` ⇄ `ClientWorker`), and the
//!   exact shape the dregg-side seam will cross.
//!
//! Scope note: the headless CLI talks to [`MatrixClient`] directly (it is already
//! an async `main`). This worker exists so the protocol foundation already
//! carries the sync-facing seam the comms-PD needs — it is wired and compiles,
//! and the UI/PD phase fills in the remaining request variants.

use std::path::PathBuf;
use std::thread::JoinHandle;

use tokio::sync::{mpsc, oneshot};

use crate::client::{MatrixClient, RoomSummary, TimelineMessage};
use crate::membrane::MembraneEnvelope;
use crate::object::DreggObject;
use crate::session::StoredSession;
use crate::Result;

/// Requests a synchronous caller can issue to the async worker.
pub enum WorkerRequest {
    /// Log in with a password; reply carries the persistable session.
    LoginPassword {
        homeserver: String,
        store_path: PathBuf,
        passphrase: String,
        username: String,
        password: String,
        device_display_name: String,
        reply: oneshot::Sender<Result<StoredSession>>,
    },
    /// Restore a persisted session.
    Restore {
        stored: StoredSession,
        reply: oneshot::Sender<Result<()>>,
    },
    /// One sync round-trip.
    SyncOnce {
        reply: oneshot::Sender<Result<()>>,
    },
    /// List joined rooms.
    JoinedRooms {
        reply: oneshot::Sender<Result<Vec<RoomSummary>>>,
    },
    /// Read a room's recent timeline.
    RecentTimeline {
        room_id: String,
        limit: u16,
        reply: oneshot::Sender<Result<Vec<TimelineMessage>>>,
    },
    /// Send a plain-text message to a room; reply carries the event id.
    SendText {
        room_id: String,
        body: String,
        reply: oneshot::Sender<Result<String>>,
    },
    /// Send a membrane-bearing message to a room; reply carries the event id.
    SendMembrane {
        room_id: String,
        body: String,
        membrane: Box<MembraneEnvelope>,
        reply: oneshot::Sender<Result<String>>,
    },
    /// Send a dregg-object-bearing message to a room; reply carries the event id.
    SendObject {
        room_id: String,
        body: String,
        object: Box<DreggObject>,
        reply: oneshot::Sender<Result<String>>,
    },
    /// The logged-in user's full id (`@user:server`), if any.
    Whoami {
        reply: oneshot::Sender<Option<String>>,
    },
    /// Create a room (optionally named/topic'd) and invite the given user ids;
    /// reply carries the new room id. The cross-user multiplayer flow A→B starts
    /// here (A creates the shared room and invites B).
    CreateRoom {
        name: Option<String>,
        topic: Option<String>,
        invites: Vec<String>,
        reply: oneshot::Sender<Result<String>>,
    },
    /// List rooms this client has been INVITED to (pending accept) — the receive
    /// side's first sight of a room A opened for it.
    InvitedRooms {
        reply: oneshot::Sender<Result<Vec<RoomSummary>>>,
    },
    /// Accept a pending invite (real join over the wire); reply carries the room id.
    AcceptInvite {
        room_id: String,
        reply: oneshot::Sender<Result<String>>,
    },
    /// Shut the worker down.
    Shutdown,
}

/// The async worker: owns the tokio runtime and the live [`MatrixClient`].
pub struct MatrixWorker;

impl MatrixWorker {
    /// Spawn the worker thread; returns a synchronous [`MatrixHandle`].
    pub fn spawn() -> std::io::Result<(MatrixHandle, JoinHandle<()>)> {
        let (tx, rx) = mpsc::unbounded_channel::<WorkerRequest>();
        let thread = std::thread::Builder::new()
            .name("deos-matrix-worker".into())
            .spawn(move || {
                let rt = tokio::runtime::Builder::new_multi_thread()
                    .enable_all()
                    .build()
                    .expect("build tokio runtime");
                rt.block_on(Self::run(rx));
            })?;
        Ok((MatrixHandle { tx }, thread))
    }

    async fn run(mut rx: mpsc::UnboundedReceiver<WorkerRequest>) {
        let mut client: Option<MatrixClient> = None;
        while let Some(req) = rx.recv().await {
            match req {
                WorkerRequest::LoginPassword {
                    homeserver,
                    store_path,
                    passphrase,
                    username,
                    password,
                    device_display_name,
                    reply,
                } => {
                    let result = MatrixClient::login_password(
                        &homeserver,
                        &store_path,
                        &passphrase,
                        &username,
                        &password,
                        &device_display_name,
                    )
                    .await;
                    let _ = reply.send(match result {
                        Ok((c, session)) => {
                            client = Some(c);
                            Ok(session)
                        }
                        Err(e) => Err(e),
                    });
                }
                WorkerRequest::Restore { stored, reply } => {
                    let _ = reply.send(match MatrixClient::restore(&stored).await {
                        Ok(c) => {
                            client = Some(c);
                            Ok(())
                        }
                        Err(e) => Err(e),
                    });
                }
                WorkerRequest::SyncOnce { reply } => {
                    let _ = reply.send(Self::with(&client, |c| c.sync_once()).await);
                }
                WorkerRequest::JoinedRooms { reply } => {
                    let _ = reply.send(Self::with(&client, |c| c.joined_rooms()).await);
                }
                WorkerRequest::RecentTimeline {
                    room_id,
                    limit,
                    reply,
                } => {
                    let _ = reply
                        .send(Self::with(&client, |c| c.recent_timeline(&room_id, limit)).await);
                }
                WorkerRequest::SendText {
                    room_id,
                    body,
                    reply,
                } => {
                    let _ = reply
                        .send(Self::with(&client, |c| c.send_text(&room_id, &body)).await);
                }
                WorkerRequest::SendMembrane {
                    room_id,
                    body,
                    membrane,
                    reply,
                } => {
                    let _ = reply.send(
                        Self::with(&client, |c| c.send_membrane(&room_id, &body, &membrane)).await,
                    );
                }
                WorkerRequest::SendObject {
                    room_id,
                    body,
                    object,
                    reply,
                } => {
                    let _ = reply.send(
                        Self::with(&client, |c| c.send_object(&room_id, &body, &object)).await,
                    );
                }
                WorkerRequest::Whoami { reply } => {
                    let me = client.as_ref().and_then(|c| c.user_id().map(|u| u.to_string()));
                    let _ = reply.send(me);
                }
                WorkerRequest::CreateRoom {
                    name,
                    topic,
                    invites,
                    reply,
                } => {
                    let _ = reply.send(
                        Self::with(&client, |c| async move {
                            let invite_refs: Vec<&str> = invites.iter().map(|s| s.as_str()).collect();
                            c.create_room(name.as_deref(), topic.as_deref(), &invite_refs).await
                        })
                        .await,
                    );
                }
                WorkerRequest::InvitedRooms { reply } => {
                    let _ = reply.send(Self::with(&client, |c| c.invited_rooms()).await);
                }
                WorkerRequest::AcceptInvite { room_id, reply } => {
                    let _ = reply
                        .send(Self::with(&client, |c| c.accept_invite(&room_id)).await);
                }
                WorkerRequest::Shutdown => break,
            }
        }
    }

    async fn with<'a, T, F, Fut>(client: &'a Option<MatrixClient>, f: F) -> Result<T>
    where
        F: FnOnce(&'a MatrixClient) -> Fut,
        Fut: std::future::Future<Output = Result<T>>,
    {
        match client {
            Some(c) => f(c).await,
            None => Err(crate::Error::Other("not logged in".into())),
        }
    }
}

/// Synchronous facade over the worker. Cloneable; each call blocks on a oneshot.
#[derive(Clone)]
pub struct MatrixHandle {
    tx: mpsc::UnboundedSender<WorkerRequest>,
}

impl MatrixHandle {
    fn call<T>(&self, build: impl FnOnce(oneshot::Sender<Result<T>>) -> WorkerRequest) -> Result<T> {
        let (reply_tx, reply_rx) = oneshot::channel();
        self.tx
            .send(build(reply_tx))
            .map_err(|_| crate::Error::Other("matrix worker is gone".into()))?;
        reply_rx
            .blocking_recv()
            .map_err(|_| crate::Error::Other("matrix worker dropped the reply".into()))?
    }

    pub fn login_password(
        &self,
        homeserver: String,
        store_path: PathBuf,
        passphrase: String,
        username: String,
        password: String,
        device_display_name: String,
    ) -> Result<StoredSession> {
        self.call(|reply| WorkerRequest::LoginPassword {
            homeserver,
            store_path,
            passphrase,
            username,
            password,
            device_display_name,
            reply,
        })
    }

    pub fn restore(&self, stored: StoredSession) -> Result<()> {
        self.call(|reply| WorkerRequest::Restore { stored, reply })
    }

    pub fn sync_once(&self) -> Result<()> {
        self.call(|reply| WorkerRequest::SyncOnce { reply })
    }

    pub fn joined_rooms(&self) -> Result<Vec<RoomSummary>> {
        self.call(|reply| WorkerRequest::JoinedRooms { reply })
    }

    pub fn recent_timeline(&self, room_id: String, limit: u16) -> Result<Vec<TimelineMessage>> {
        self.call(|reply| WorkerRequest::RecentTimeline {
            room_id,
            limit,
            reply,
        })
    }

    pub fn send_text(&self, room_id: String, body: String) -> Result<String> {
        self.call(|reply| WorkerRequest::SendText {
            room_id,
            body,
            reply,
        })
    }

    pub fn send_membrane(
        &self,
        room_id: String,
        body: String,
        membrane: MembraneEnvelope,
    ) -> Result<String> {
        self.call(|reply| WorkerRequest::SendMembrane {
            room_id,
            body,
            membrane: Box::new(membrane),
            reply,
        })
    }

    pub fn send_object(
        &self,
        room_id: String,
        body: String,
        object: DreggObject,
    ) -> Result<String> {
        self.call(|reply| WorkerRequest::SendObject {
            room_id,
            body,
            object: Box::new(object),
            reply,
        })
    }

    /// The logged-in user's full id, if the worker holds an authenticated client.
    pub fn whoami(&self) -> Option<String> {
        let (reply_tx, reply_rx) = oneshot::channel();
        if self.tx.send(WorkerRequest::Whoami { reply: reply_tx }).is_err() {
            return None;
        }
        reply_rx.blocking_recv().ok().flatten()
    }

    /// Create a room and invite the given full user ids; returns the new room id.
    pub fn create_room(
        &self,
        name: Option<String>,
        topic: Option<String>,
        invites: Vec<String>,
    ) -> Result<String> {
        self.call(|reply| WorkerRequest::CreateRoom {
            name,
            topic,
            invites,
            reply,
        })
    }

    /// List rooms this client has a pending invite to.
    pub fn invited_rooms(&self) -> Result<Vec<RoomSummary>> {
        self.call(|reply| WorkerRequest::InvitedRooms { reply })
    }

    /// Accept a pending invite (real join over the wire); returns the room id.
    pub fn accept_invite(&self, room_id: String) -> Result<String> {
        self.call(|reply| WorkerRequest::AcceptInvite { room_id, reply })
    }

    /// Ask the worker to stop. The caller may then `join` the worker thread.
    pub fn shutdown(&self) {
        let _ = self.tx.send(WorkerRequest::Shutdown);
    }
}
