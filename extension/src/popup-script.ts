/**
 * Popup script for the Dragon's Egg cipherclerk extension UI.
 * Communicates with the background service worker via chrome.runtime.sendMessage.
 */

import type { CipherclerkState, OriginPermissionDisplay, ProfileInfo, ReceiptEventSummary } from "./types";

// ---------------------------------------------------------------------------
// DOM Elements
// ---------------------------------------------------------------------------

const statusDot = document.getElementById("statusDot")!;
const statusText = document.getElementById("statusText")!;
const wasmError = document.getElementById("wasmError") as HTMLElement;
const tokenCount = document.getElementById("tokenCount")!;
const chainLength = document.getElementById("chainLength")!;
const logContainer = document.getElementById("logContainer")!;
const lockBtn = document.getElementById("lockBtn")!;
const backupBtn = document.getElementById("backupBtn")!;
const recoverBtn = document.getElementById("recoverBtn")!;
const managePermsBtn = document.getElementById("managePermsBtn")!;
const passphraseSection = document.getElementById("passphraseSection")!;
const passphraseInput = document.getElementById("passphraseInput") as HTMLInputElement;
const passphraseSetupSection = document.getElementById("passphraseSetupSection")!;
const newPassphraseInput = document.getElementById("newPassphraseInput") as HTMLInputElement;
const confirmPassphraseInput = document.getElementById("confirmPassphraseInput") as HTMLInputElement;
const setPassphraseBtn = document.getElementById("setPassphraseBtn")!;
const mnemonicDisplay = document.getElementById("mnemonicDisplay")!;
const mnemonicWarning = document.getElementById("mnemonicWarning")!;
const permissionsSection = document.getElementById("permissionsSection")!;
const permissionsContainer = document.getElementById("permissionsContainer")!;
const settingsBtn = document.getElementById("settingsBtn")!;
const intentsBtn = document.getElementById("intentsBtn")!;
const intentsSection = document.getElementById("intentsSection")!;
const intentsContainer = document.getElementById("intentsContainer")!;
const profileSelect = document.getElementById("profileSelect") as HTMLSelectElement;
const profilePubkey = document.getElementById("profilePubkey")!;
const newProfileName = document.getElementById("newProfileName") as HTMLInputElement;
const createProfileBtn = document.getElementById("createProfileBtn") as HTMLButtonElement;
const profileError = document.getElementById("profileError")!;
const receiptsContainer = document.getElementById("receiptsContainer")!;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

async function sendMessage<T = unknown>(type: string, extra: Record<string, unknown> = {}): Promise<T | undefined> {
  const id = `popup_${Date.now()}`;
  const response = await chrome.runtime.sendMessage({ type, id, ...extra });
  return response?.result as T | undefined;
}

function escapeHtml(str: string): string {
  return String(str)
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/"/g, "&quot;");
}

// ---------------------------------------------------------------------------
// Refresh state
// ---------------------------------------------------------------------------

async function refresh(): Promise<void> {
  const state = await sendMessage<CipherclerkState>("dregg:getState");
  if (!state) return;

  // Surface WASM load failures: every signing / proof / key-derivation
  // operation depends on the WASM crypto module, so make the failure visible
  // rather than letting the user hit cryptic per-operation errors.
  if (wasmError) {
    if (state.wasmReady === false) {
      wasmError.textContent = state.wasmError
        ? `Cryptographic module failed to load: ${state.wasmError}. Cipherclerk operations requiring proofs or key derivation are unavailable.`
        : "Cryptographic module failed to load. Cipherclerk operations requiring proof generation or key derivation are unavailable. Ensure your browser supports WebAssembly.";
      wasmError.style.display = "block";
    } else {
      wasmError.style.display = "none";
    }
  }

  if (state.locked) {
    statusDot.classList.add("locked");
    statusText.textContent = "Locked";
    lockBtn.textContent = "Unlock Cipherclerk";
    lockBtn.classList.add("locked");
    passphraseSection.classList.remove("hidden");
    passphraseSetupSection.classList.add("hidden");
    backupBtn.style.display = "none";
    mnemonicDisplay.style.display = "none";
    mnemonicWarning.style.display = "none";
    permissionsSection.style.display = "none";
  } else {
    statusDot.classList.remove("locked");
    statusText.textContent = "Connected";
    lockBtn.textContent = "Lock Cipherclerk";
    lockBtn.classList.remove("locked");
    passphraseSection.classList.add("hidden");
    backupBtn.style.display = state.hasMnemonic ? "block" : "none";
    if (state.needsPassphraseSetup) {
      passphraseSetupSection.classList.remove("hidden");
    } else {
      passphraseSetupSection.classList.add("hidden");
    }
  }
  tokenCount.textContent = String(state.tokenCount);
  chainLength.textContent = String(state.chainLength);
}

// ---------------------------------------------------------------------------
// Log
// ---------------------------------------------------------------------------

interface LogEntryDisplay {
  action: string;
  resource: string;
  allowed: boolean;
  timestamp: number;
}

async function loadLog(): Promise<void> {
  // The activity log lives in the encrypted, in-memory cipherclerk state — the
  // plaintext `dregg_cipherclerk` storage key is removed after migration, so it
  // must be fetched via the background `dregg:getLog` message (returns [] while
  // locked). `getLog` already returns newest-first.
  const log = await sendMessage<LogEntryDisplay[]>("dregg:getLog");
  if (!log || log.length === 0) {
    logContainer.innerHTML = '<div class="empty">No recent authorizations</div>';
    return;
  }
  const entries = log.slice(0, 5);
  logContainer.innerHTML = entries.map(entry => {
    const time = new Date(entry.timestamp).toLocaleTimeString();
    const icon = entry.allowed ? "&#x2713;" : "&#x2717;";
    return `<div class="log-entry"><span>${icon} ${escapeHtml(entry.action)} on ${escapeHtml(entry.resource)}</span><div class="time">${escapeHtml(time)}</div></div>`;
  }).join("");
}

// ---------------------------------------------------------------------------
// Identity profiles (mirrors `dregg id create / list / use`)
// ---------------------------------------------------------------------------

function showProfileError(text: string): void {
  profileError.textContent = text;
  profileError.style.display = text ? "block" : "none";
}

function renderProfiles(profiles: ProfileInfo[]): void {
  profileSelect.innerHTML = "";
  if (!profiles || profiles.length === 0) {
    const opt = document.createElement("option");
    opt.value = "";
    opt.textContent = "--";
    profileSelect.appendChild(opt);
    profilePubkey.textContent = "";
    return;
  }
  for (const p of profiles) {
    const opt = document.createElement("option");
    opt.value = p.name;
    opt.textContent = p.active ? `${p.name} (active)` : p.name;
    if (p.active) opt.selected = true;
    profileSelect.appendChild(opt);
  }
  const active = profiles.find(p => p.active);
  profilePubkey.textContent = active ? active.publicKeyHex : "";
}

async function loadProfiles(): Promise<void> {
  const profiles = await sendMessage<ProfileInfo[]>("dregg:listProfiles");
  renderProfiles(profiles || []);
}

profileSelect.addEventListener("change", async () => {
  const name = profileSelect.value;
  if (!name) return;
  showProfileError("");
  const result = await sendMessage<{ active?: string; error?: string }>("dregg:useProfile", { name });
  if (result?.error) {
    showProfileError(result.error);
  }
  await loadProfiles();
  await loadReceipts();
});

createProfileBtn.addEventListener("click", async () => {
  const name = newProfileName.value.trim();
  if (!name) return;
  showProfileError("");
  createProfileBtn.disabled = true;
  const result = await sendMessage<{ created?: ProfileInfo; error?: string }>("dregg:createProfile", { name });
  createProfileBtn.disabled = false;
  if (result?.error) {
    showProfileError(result.error);
    return;
  }
  newProfileName.value = "";
  await loadProfiles();
});

// ---------------------------------------------------------------------------
// Recent receipts (node SSE /api/events/stream; reading clears the badge)
// ---------------------------------------------------------------------------

async function loadReceipts(): Promise<void> {
  const result = await sendMessage<{ receipts: ReceiptEventSummary[]; unseen: number }>("dregg:getRecentReceipts");
  const receipts = result?.receipts || [];
  if (receipts.length === 0) {
    receiptsContainer.innerHTML = '<div class="empty">No receipts observed yet</div>';
    return;
  }
  receiptsContainer.innerHTML = receipts.slice(0, 8).map(r => {
    const short = r.receiptHash ? r.receiptHash.slice(0, 12) + "..." : "?";
    const kinds = r.kinds && r.kinds.length > 0 ? r.kinds.join(", ") : "(no effect summary)";
    const time = r.timestamp ? new Date(r.timestamp * 1000).toLocaleTimeString() : "";
    const proof = r.hasProof ? " &#x2713;proof" : "";
    return `<div class="log-entry">
      <span style="font-family:monospace;color:#a78bfa;" title="${escapeHtml(r.receiptHash)}">${escapeHtml(short)}</span>
      <span style="font-size:11px;"> ${escapeHtml(kinds)}${proof}</span>
      <div class="time">${escapeHtml(r.finality || "")} · h${r.height} · ${escapeHtml(time)}</div>
    </div>`;
  }).join("");
}

// ---------------------------------------------------------------------------
// Lock / Unlock
// ---------------------------------------------------------------------------

lockBtn.addEventListener("click", async () => {
  const state = await sendMessage<CipherclerkState>("dregg:getState");
  if (!state) return;

  if (state.locked) {
    const passphrase = passphraseInput.value;
    const result = await sendMessage<{ success: boolean }>("dregg:unlock", { passphrase });
    if (result && !result.success) {
      passphraseInput.style.borderColor = "#f87171";
      passphraseInput.value = "";
      passphraseInput.placeholder = "Invalid passphrase - try again";
      return;
    }
    passphraseInput.value = "";
    passphraseInput.style.borderColor = "";
    passphraseInput.placeholder = "Enter passphrase to unlock";
  } else {
    await sendMessage("dregg:lock");
  }
  await refresh();
  await loadLog();
  await loadProfiles();
  await loadReceipts();
});

// ---------------------------------------------------------------------------
// Passphrase setup
// ---------------------------------------------------------------------------

setPassphraseBtn.addEventListener("click", async () => {
  const newPass = newPassphraseInput.value;
  const confirmPass = confirmPassphraseInput.value;
  if (!newPass) {
    newPassphraseInput.style.borderColor = "#f87171";
    newPassphraseInput.placeholder = "Passphrase is required";
    return;
  }
  if (newPass !== confirmPass) {
    confirmPassphraseInput.style.borderColor = "#f87171";
    confirmPassphraseInput.value = "";
    confirmPassphraseInput.placeholder = "Passphrases do not match";
    return;
  }
  await sendMessage("dregg:setPassphrase", { passphrase: newPass });
  newPassphraseInput.value = "";
  confirmPassphraseInput.value = "";
  newPassphraseInput.style.borderColor = "";
  confirmPassphraseInput.style.borderColor = "";
  passphraseSetupSection.classList.add("hidden");
  await refresh();
});

// ---------------------------------------------------------------------------
// Permissions management
// ---------------------------------------------------------------------------

managePermsBtn.addEventListener("click", async () => {
  if (permissionsSection.style.display === "none") {
    permissionsSection.style.display = "block";
    managePermsBtn.textContent = "Hide Permissions";
    await loadPermissions();
  } else {
    permissionsSection.style.display = "none";
    managePermsBtn.textContent = "Manage Permissions";
  }
});

async function loadPermissions(): Promise<void> {
  const perms = await sendMessage<OriginPermissionDisplay[]>("dregg:getOriginPermissions");
  if (!perms || perms.length === 0) {
    permissionsContainer.innerHTML = '<div class="empty">No origins approved</div>';
    return;
  }
  permissionsContainer.innerHTML = perms.map(p => {
    const expiresIn = p.expiresIn ? Math.round(p.expiresIn / 60000) : 0;
    const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
    return `<div class="log-entry" style="display:flex;justify-content:space-between;align-items:center;">
      <div>
        <div style="font-size:11px;color:#fbbf24;word-break:break-all;">${escapeHtml(p.origin)}</div>
        <div class="time">${escapeHtml(p.methods.join(", "))} - expires in ${expiresStr}</div>
      </div>
      <button class="revoke-btn" data-origin="${escapeHtml(p.origin)}" style="flex-shrink:0;padding:4px 8px;font-size:11px;background:#7f1d1d;color:#fca5a5;border:none;border-radius:4px;cursor:pointer;">Revoke</button>
    </div>`;
  }).join("");

  permissionsContainer.querySelectorAll(".revoke-btn").forEach(btn => {
    btn.addEventListener("click", async () => {
      await sendMessage("dregg:revokeOriginPermission", { origin: (btn as HTMLElement).dataset.origin });
      await loadPermissions();
    });
  });
}

// ---------------------------------------------------------------------------
// Backup / Recovery
// ---------------------------------------------------------------------------

backupBtn.addEventListener("click", async () => {
  const state = await sendMessage<CipherclerkState>("dregg:getState");
  if (state && state.locked) {
    alert("Unlock your cipherclerk first to view the recovery phrase.");
    return;
  }
  const mnemonic = await sendMessage<string>("dregg:getMnemonic");
  if (!mnemonic) {
    alert("No recovery phrase available for this cipherclerk.");
    return;
  }
  if (mnemonicDisplay.style.display === "block") {
    mnemonicDisplay.style.display = "none";
    mnemonicWarning.style.display = "none";
    backupBtn.textContent = "Backup (Show Recovery Phrase)";
  } else {
    const words = mnemonic.split(" ");
    mnemonicDisplay.innerHTML = words.map((w, i) =>
      `<span>${String(i + 1).padStart(2, "0")}. ${w}</span>`
    ).join("&nbsp;&nbsp;");
    mnemonicDisplay.style.display = "block";
    mnemonicWarning.style.display = "block";
    backupBtn.textContent = "Hide Recovery Phrase";
  }
});

recoverBtn.addEventListener("click", () => {
  chrome.tabs.create({ url: chrome.runtime.getURL("recovery.html") });
});

settingsBtn.addEventListener("click", () => {
  chrome.tabs.create({ url: chrome.runtime.getURL("settings.html") });
});

// ---------------------------------------------------------------------------
// Intents
// ---------------------------------------------------------------------------

interface FulfillableIntent {
  intentId: string;
  grantedActions: string[];
  resource: string;
  expiry: number;
  matchedTokenId: string;
}

intentsBtn.addEventListener("click", async () => {
  if (intentsSection.style.display === "none") {
    intentsSection.style.display = "block";
    intentsBtn.textContent = "Hide Intents";
    await loadFulfillableIntents();
  } else {
    intentsSection.style.display = "none";
    intentsBtn.textContent = "Fulfill Intents";
  }
});

async function loadFulfillableIntents(): Promise<void> {
  const intents = await sendMessage<FulfillableIntent[]>("dregg:getFulfillableIntents");
  if (!intents || intents.length === 0) {
    intentsContainer.innerHTML = '<div class="empty">No fulfillable intents available</div>';
    return;
  }
  intentsContainer.innerHTML = intents.map(item => {
    const actions = item.grantedActions ? item.grantedActions.join(", ") : "any";
    const expiresIn = Math.max(0, Math.round((item.expiry - Date.now()) / 60000));
    const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
    const shortId = item.intentId.slice(0, 12) + "...";
    return `<div class="log-entry" style="display:flex;justify-content:space-between;align-items:center;">
      <div>
        <div style="font-size:11px;color:#a78bfa;word-break:break-all;" title="${escapeHtml(item.intentId)}">${escapeHtml(shortId)}</div>
        <div class="time">${escapeHtml(actions)} on ${escapeHtml(item.resource)} - expires in ${expiresStr}</div>
      </div>
      <button class="fulfill-btn" data-intent-id="${escapeHtml(item.intentId)}" data-token-id="${escapeHtml(item.matchedTokenId)}" style="flex-shrink:0;padding:4px 8px;font-size:11px;background:#065f46;color:#6ee7b7;border:none;border-radius:4px;cursor:pointer;">Fulfill</button>
    </div>`;
  }).join("");

  intentsContainer.querySelectorAll(".fulfill-btn").forEach(btn => {
    btn.addEventListener("click", async () => {
      const button = btn as HTMLButtonElement;
      button.disabled = true;
      button.textContent = "...";
      const result = await sendMessage<{ fulfilled?: boolean }>("dregg:fulfillIntent", {
        intentId: button.dataset.intentId,
        tokenId: button.dataset.tokenId,
      });
      if (result && result.fulfilled) {
        button.textContent = "Done";
        button.style.background = "#064e3b";
        setTimeout(() => loadFulfillableIntents(), 1000);
      } else {
        button.textContent = "Failed";
        button.style.background = "#7f1d1d";
        button.style.color = "#fca5a5";
        button.disabled = false;
        setTimeout(() => {
          button.textContent = "Fulfill";
          button.style.background = "#065f46";
          button.style.color = "#6ee7b7";
        }, 3000);
      }
    });
  });
}

// ---------------------------------------------------------------------------
// Tab navigation
// ---------------------------------------------------------------------------

const tabButtons = document.querySelectorAll(".tab-btn");
const tabContents = document.querySelectorAll(".tab-content");

tabButtons.forEach(btn => {
  btn.addEventListener("click", () => {
    const tabId = (btn as HTMLElement).dataset.tab;
    tabButtons.forEach(b => b.classList.remove("active"));
    tabContents.forEach(c => c.classList.remove("active"));
    btn.classList.add("active");
    document.getElementById(`tab-${tabId}`)?.classList.add("active");

    if (tabId === "account") loadAccount();
    if (tabId === "capabilities") loadLiveRefs();
    if (tabId === "directory") loadDirectory();
    if (tabId === "storage") loadStorageQuota();
  });
});

// ---------------------------------------------------------------------------
// Account / Devnet tab
//
// Routes through the node's REAL verified executor via the background
// node-API handlers. JSON turns submitted here are signed by the node
// operator's cipherclerk (the node ignores the body agent — confused-deputy
// hardening), so this surfaces the operator's agent cell: the identity whose
// turns actually commit on the devnet node the extension is pointed at.
// ---------------------------------------------------------------------------

const acctNodeUrl = document.getElementById("acctNodeUrl")!;
const acctUnlocked = document.getElementById("acctUnlocked")!;
const acctCell = document.getElementById("acctCell")!;
const acctBalance = document.getElementById("acctBalance")!;
const acctNonce = document.getElementById("acctNonce")!;
const acctRefreshBtn = document.getElementById("acctRefreshBtn") as HTMLButtonElement;
const acctFaucetBtn = document.getElementById("acctFaucetBtn") as HTMLButtonElement;
const acctSendTo = document.getElementById("acctSendTo") as HTMLInputElement;
const acctSendAmount = document.getElementById("acctSendAmount") as HTMLInputElement;
const acctSendBtn = document.getElementById("acctSendBtn") as HTMLButtonElement;
const acctResult = document.getElementById("acctResult") as HTMLElement;

interface NodeIdentity {
  publicKey: string;
  agentCell: string;
  unlocked: boolean;
  agentBalance: number | null;
  agentNonce: number | null;
  error?: string;
}

let cachedIdentity: NodeIdentity | null = null;

function showAcctResult(html: string, color: string): void {
  acctResult.innerHTML = html;
  acctResult.style.color = color;
  acctResult.style.display = "block";
}

async function loadAccount(): Promise<void> {
  const cfg = await sendMessage<{ nodeUrl?: string }>("dregg:getNodeConfig");
  acctNodeUrl.textContent = cfg?.nodeUrl || "(unset)";

  const id = await sendMessage<NodeIdentity>("dregg:nodeIdentity");
  cachedIdentity = id ?? null;
  if (!id || id.error || !id.agentCell) {
    acctUnlocked.textContent = "offline";
    acctCell.textContent = id?.error ? `Node unreachable: ${id.error}` : "--";
    acctBalance.textContent = "--";
    acctNonce.textContent = "--";
    return;
  }
  acctUnlocked.textContent = id.unlocked ? "unlocked" : "locked (set passphrase on node)";
  acctCell.textContent = id.agentCell;
  acctBalance.textContent = id.agentBalance == null ? "0 (cell not materialized)" : String(id.agentBalance);
  acctNonce.textContent = id.agentNonce == null ? "0" : String(id.agentNonce);
}

acctRefreshBtn.addEventListener("click", loadAccount);

acctFaucetBtn.addEventListener("click", async () => {
  if (!cachedIdentity?.agentCell) {
    showAcctResult("Load the account first (node unreachable).", "#f87171");
    return;
  }
  acctFaucetBtn.disabled = true;
  acctFaucetBtn.textContent = "Funding...";
  // Pass the operator pubkey so the cell is materialized with a real key —
  // otherwise later operator-signed turns fail Ed25519 verification.
  const result = await sendMessage<{ success: boolean; amount?: number; error?: string }>("dregg:faucetFund", {
    cellId: cachedIdentity.agentCell,
    amount: 1000,
    publicKey: cachedIdentity.publicKey,
  });
  acctFaucetBtn.disabled = false;
  acctFaucetBtn.textContent = "Faucet: fund 1000 DEC";
  if (result?.success) {
    showAcctResult(`Funded ${result.amount ?? 0} DEC.`, "#6ee7b7");
    setTimeout(loadAccount, 1500);
  } else {
    showAcctResult(`Faucet failed: ${escapeHtml(result?.error || "unknown")}`, "#f87171");
  }
});

acctSendBtn.addEventListener("click", async () => {
  if (!cachedIdentity?.agentCell) {
    showAcctResult("Load the account first (node unreachable).", "#f87171");
    return;
  }
  const to = acctSendTo.value.trim();
  const amount = parseInt(acctSendAmount.value, 10);
  if (!/^[0-9a-fA-F]{64}$/.test(to)) {
    showAcctResult("Recipient must be a 64-char hex cell ID.", "#f87171");
    return;
  }
  if (!Number.isFinite(amount) || amount <= 0) {
    showAcctResult("Amount must be a positive integer.", "#f87171");
    return;
  }
  acctSendBtn.disabled = true;
  acctSendBtn.textContent = "Submitting...";
  // fee is the computron budget; a single transfer needs ~300, use 500 headroom.
  const nonce = cachedIdentity.agentNonce == null ? 0 : cachedIdentity.agentNonce;
  const result = await sendMessage<{
    accepted: boolean;
    turnHash?: string;
    proofStatus?: string;
    witnessCount?: number;
    error?: string;
  }>("dregg:submitJsonTurn", {
    spec: {
      agent: cachedIdentity.agentCell,
      nonce,
      fee: 500,
      memo: "extension transfer",
      effects: [{ kind: "transfer", to, amount }],
    },
  });
  acctSendBtn.disabled = false;
  acctSendBtn.textContent = "Send";
  if (result?.accepted && result.turnHash) {
    const short = result.turnHash.slice(0, 16);
    showAcctResult(
      `Committed turn <code>${escapeHtml(short)}...</code> (${escapeHtml(result.proofStatus || "?")}, ${result.witnessCount ?? 0} witness).`,
      "#6ee7b7",
    );
    acctSendTo.value = "";
    acctSendAmount.value = "";
    setTimeout(loadAccount, 1500);
  } else {
    showAcctResult(`Rejected: ${escapeHtml(result?.error || "unknown error")}`, "#f87171");
  }
});

// ---------------------------------------------------------------------------
// Capabilities tab
// ---------------------------------------------------------------------------

const liveRefsContainer = document.getElementById("liveRefsContainer")!;
const acceptUriInput = document.getElementById("acceptUriInput") as HTMLInputElement;
const acceptCapBtn = document.getElementById("acceptCapBtn")!;
const shareCellInput = document.getElementById("shareCellInput") as HTMLInputElement;
const shareCapBtn = document.getElementById("shareCapBtn")!;
const shareResult = document.getElementById("shareResult")!;
const shareResultUri = document.getElementById("shareResultUri")!;
const copyUriBtn = document.getElementById("copyUriBtn")!;

interface LiveRefDisplay {
  refId: string;
  cellId: string;
  nodeId: string;
  createdAt: number;
}

async function loadLiveRefs(): Promise<void> {
  const refs = await sendMessage<LiveRefDisplay[]>("dregg:getLiveRefs");
  if (!refs || refs.length === 0) {
    liveRefsContainer.innerHTML = '<div class="empty">No live references held</div>';
    return;
  }
  liveRefsContainer.innerHTML = refs.map(r => {
    const shortCell = r.cellId ? (r.cellId.slice(0, 12) + "..." + r.cellId.slice(-4)) : "?";
    const age = Math.round((Date.now() - r.createdAt) / 60000);
    const ageStr = age > 60 ? `${Math.round(age / 60)}h ago` : `${age}m ago`;
    return `<div class="ref-item">
      <div class="ref-cell">${escapeHtml(shortCell)}</div>
      <div class="ref-meta">Node: ${escapeHtml(r.nodeId || "?")} | ${ageStr}</div>
      <button class="small-btn danger drop-ref-btn" data-ref-id="${escapeHtml(r.refId)}" style="margin-top: 4px;">Drop</button>
    </div>`;
  }).join("");

  liveRefsContainer.querySelectorAll(".drop-ref-btn").forEach(btn => {
    btn.addEventListener("click", async () => {
      await sendMessage("dregg:dropLiveRef", { refId: (btn as HTMLElement).dataset.refId });
      await loadLiveRefs();
    });
  });
}

acceptCapBtn.addEventListener("click", async () => {
  const uri = acceptUriInput.value.trim();
  if (!uri) return;
  acceptCapBtn.textContent = "...";
  (acceptCapBtn as HTMLButtonElement).disabled = true;
  const result = await sendMessage<{ error?: string }>("dregg:acceptCapability", { uri });
  if (result && !result.error) {
    acceptUriInput.value = "";
    acceptCapBtn.textContent = "Accepted!";
    setTimeout(() => {
      acceptCapBtn.textContent = "Accept Capability";
      (acceptCapBtn as HTMLButtonElement).disabled = false;
    }, 2000);
    await loadLiveRefs();
  } else {
    acceptCapBtn.textContent = result?.error || "Failed";
    setTimeout(() => {
      acceptCapBtn.textContent = "Accept Capability";
      (acceptCapBtn as HTMLButtonElement).disabled = false;
    }, 3000);
  }
});

shareCapBtn.addEventListener("click", async () => {
  const cellId = shareCellInput.value.trim();
  if (!cellId || !/^[0-9a-fA-F]{64}$/.test(cellId)) {
    shareCellInput.style.borderColor = "#f87171";
    shareCellInput.placeholder = "Enter valid 64-char hex cell ID";
    return;
  }
  shareCellInput.style.borderColor = "";
  shareCapBtn.textContent = "...";
  (shareCapBtn as HTMLButtonElement).disabled = true;
  const result = await sendMessage<{ uri?: string; error?: string }>("dregg:shareCapability", { cellId });
  shareCapBtn.textContent = "Share as URI";
  (shareCapBtn as HTMLButtonElement).disabled = false;
  if (result && result.uri) {
    shareResultUri.textContent = result.uri;
    shareResult.style.display = "block";
  } else {
    shareResultUri.textContent = result?.error || "Failed to generate URI";
    shareResult.style.display = "block";
  }
});

copyUriBtn.addEventListener("click", () => {
  const uri = shareResultUri.textContent || "";
  navigator.clipboard.writeText(uri).then(() => {
    copyUriBtn.textContent = "Copied!";
    setTimeout(() => { copyUriBtn.textContent = "Copy URI"; }, 2000);
  });
});

// ---------------------------------------------------------------------------
// Directory tab
// ---------------------------------------------------------------------------

const directoryContainer = document.getElementById("directoryContainer")!;
const discoverTagsInput = document.getElementById("discoverTagsInput") as HTMLInputElement;
const discoverBtn = document.getElementById("discoverBtn")!;
const discoveryResults = document.getElementById("discoveryResults")!;

async function loadDirectory(): Promise<void> {
  const result = await sendMessage<{ entries?: Array<{ name?: string; path?: string; kind?: string; version?: number }> }>("dregg:resolvePath", { path: "/" });
  if (result && result.entries) {
    const entries = result.entries || [];
    if (entries.length === 0) {
      directoryContainer.innerHTML = '<div class="empty">No services mounted</div>';
    } else {
      directoryContainer.innerHTML = entries.map(e => {
        return `<div class="dir-item">
          <div class="dir-path">${escapeHtml(e.name || e.path || "?")}</div>
          <div class="dir-kind">${escapeHtml(e.kind || "-")} | v${e.version || 0}</div>
        </div>`;
      }).join("");
    }
  } else {
    directoryContainer.innerHTML = '<div class="empty">Could not load directory</div>';
  }
}

discoverBtn.addEventListener("click", async () => {
  const tagsStr = discoverTagsInput.value.trim();
  const tags = tagsStr ? tagsStr.split(",").map(t => t.trim()).filter(Boolean) : [];
  discoverBtn.textContent = "...";
  (discoverBtn as HTMLButtonElement).disabled = true;
  const result = await sendMessage<{ results?: Array<{ path?: string; name?: string; kind?: string }> }>("dregg:discoverServices", { tags });
  discoverBtn.textContent = "Search";
  (discoverBtn as HTMLButtonElement).disabled = false;

  if (result && result.results && result.results.length > 0) {
    discoveryResults.innerHTML = result.results.map(r => {
      return `<div class="dir-item">
        <div class="dir-path">${escapeHtml(r.path || r.name || "?")}</div>
        <div class="dir-kind">${escapeHtml(r.kind || "-")}</div>
      </div>`;
    }).join("");
  } else {
    discoveryResults.innerHTML = '<div class="empty">No results found</div>';
  }
});

// ---------------------------------------------------------------------------
// Storage tab
// ---------------------------------------------------------------------------

const quotaBytesStored = document.getElementById("quotaBytesStored")!;
const quotaBytesLimit = document.getElementById("quotaBytesLimit")!;
const quotaBarFill = document.getElementById("quotaBarFill") as HTMLElement;
const quotaObjectCount = document.getElementById("quotaObjectCount")!;
const quotaComputrons = document.getElementById("quotaComputrons")!;
const refreshQuotaBtn = document.getElementById("refreshQuotaBtn")!;

function formatBytes(bytes: number): string {
  if (bytes === 0) return "0 B";
  const units = ["B", "KB", "MB", "GB"];
  const i = Math.floor(Math.log(bytes) / Math.log(1024));
  return `${(bytes / Math.pow(1024, i)).toFixed(1)} ${units[i]}`;
}

interface StorageQuotaDisplay {
  bytesStored: number;
  bytesLimit: number;
  objectCount: number;
  computronsRemaining: number;
  error?: string;
}

async function loadStorageQuota(): Promise<void> {
  const result = await sendMessage<StorageQuotaDisplay>("dregg:storageQuota", {});
  if (result && !result.error) {
    quotaBytesStored.textContent = formatBytes(result.bytesStored || 0);
    quotaBytesLimit.textContent = formatBytes(result.bytesLimit || 0);
    quotaObjectCount.textContent = String(result.objectCount || 0);
    quotaComputrons.textContent = String(result.computronsRemaining || 0);
    const pct = result.bytesLimit > 0
      ? Math.round((result.bytesStored / result.bytesLimit) * 100)
      : 0;
    quotaBarFill.style.width = `${Math.min(pct, 100)}%`;
    if (pct > 90) quotaBarFill.style.background = "#f87171";
  } else {
    quotaBytesStored.textContent = "--";
    quotaBytesLimit.textContent = "--";
    quotaObjectCount.textContent = "--";
    quotaComputrons.textContent = "--";
  }
}

refreshQuotaBtn.addEventListener("click", loadStorageQuota);

// ---------------------------------------------------------------------------
// Initialize
// ---------------------------------------------------------------------------

refresh();
loadLog();
loadProfiles();
loadReceipts();
