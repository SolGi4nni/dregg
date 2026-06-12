import express from 'express';
import type { Server } from 'http';

/**
 * Mock dregg node HTTP server for deterministic testing.
 * Simulates all endpoints the extension calls.
 */

export interface MockNodeOptions {
  port?: number;
}

export interface MockNodeState {
  balance: number;
  tokens: Array<{ id: string; actions: string[]; resource: string }>;
  quota: {
    bytesStored: number;
    bytesLimit: number;
    objectCount: number;
    computronsRemaining: number;
  };
  services: Array<{ name: string; path: string; kind: string; version: number; tags: string[] }>;
  storedFiles: Map<string, string>; // hash -> base64 content
  lastSubmittedTurn: any;
  lastMountRequest: any;
  lastBearerAuth: any;
  lastPeerExchange: any;
}

export class MockNode {
  private app: express.Express;
  private server: Server | null = null;
  private port: number;
  state: MockNodeState;

  constructor(opts: MockNodeOptions = {}) {
    this.port = opts.port || 8420;
    this.state = this.defaultState();
    this.app = express();
    this.app.use(express.json());
    // Signed-turn envelopes arrive as raw postcard bytes.
    this.app.use(express.raw({ type: 'application/octet-stream', limit: '4mb' }));
    this.setupRoutes();
  }

  private defaultState(): MockNodeState {
    return {
      balance: 1000,
      tokens: [
        { id: 'tok_mock_001', actions: ['read', 'write'], resource: 'documents/*' },
        { id: 'tok_mock_002', actions: ['transfer'], resource: 'cipherclerk/balance' },
      ],
      quota: {
        // A visible fraction (50%) so the popup's quota bar renders nonzero.
        bytesStored: 524288,
        bytesLimit: 1048576,
        objectCount: 3,
        computronsRemaining: 500000,
      },
      services: [
        { name: 'oracle-price', path: '/services/oracle-price', kind: 'oracle', version: 1, tags: ['oracle', 'price'] },
        { name: 'storage-node', path: '/services/storage', kind: 'storage', version: 2, tags: ['storage', 'cas'] },
      ],
      storedFiles: new Map(),
      lastSubmittedTurn: null,
      lastMountRequest: null,
      lastBearerAuth: null,
      lastPeerExchange: null,
    };
  }

  private setupRoutes() {
    // Health / status endpoint. The extension speaks the gateway-reachable
    // /api/node/status alias (the real node serves both; the public Caddy
    // forwards only /api/-prefixed routes).
    const status = (_req: express.Request, res: express.Response) => {
      res.json({
        ok: true,
        version: '0.1.0-mock',
        public_key: '11'.repeat(32),
        federation_mode: 'single',
        latest_height: 42,
        merkle_root: 'abcdef0123456789abcdef0123456789abcdef0123456789abcdef0123456789',
        height: 42,
        peer_count: 3,
      });
    };
    this.app.get('/status', status);
    this.app.get('/api/node/status', status);
    this.app.get('/api/node/health', status);

    // Node operator identity.
    this.app.get('/api/node/identity', (_req, res) => {
      res.json({
        public_key: '11'.repeat(32),
        agent_cell: '22'.repeat(32),
        unlocked: true,
        agent_balance: 1_000_000,
        agent_nonce: 7,
      });
    });

    // Faucet.
    this.app.post('/api/faucet', (req, res) => {
      res.json({ success: true, amount: req.body?.amount ?? 1000, tx_hash: 'mock_faucet_tx' });
    });

    // Signed-turn envelope ingress (postcard bytes; the node's
    // POST /api/turns/submit-signed). Mirrors SubmitSignedTurnResponse.
    this.app.post('/api/turns/submit-signed', (req, res) => {
      this.state.lastSubmittedTurn = req.body; // Buffer of envelope bytes
      res.json({
        accepted: true,
        turn_hash: 'ab'.repeat(32),
        signer: '11'.repeat(32),
        action_count: 1,
        proof_status: 'pending',
        has_witness: false,
        witness_count: 0,
        error: null,
      });
    });

    // Receipt stream (the node's GET /api/events/stream, SSE). The mock
    // sends a heartbeat comment and holds the connection open.
    this.app.get('/api/events/stream', (_req, res) => {
      res.writeHead(200, {
        'Content-Type': 'text/event-stream',
        'Cache-Control': 'no-cache',
        Connection: 'keep-alive',
      });
      res.write(': hb\n\n');
      // Held open until the client or server closes.
    });

    // Cipherclerk balance.
    this.app.get('/cipherclerk/balance', (_req, res) => {
      res.json({ balance: this.state.balance });
    });

    // Submit a turn.
    this.app.post('/turns/submit', (req, res) => {
      this.state.lastSubmittedTurn = req.body;
      const turnId = `turn_${Date.now()}_mock`;
      res.json({ turn_id: turnId, accepted: true, receipt: 'mock_receipt_hash' });
    });

    // Bearer auth (export sturdy ref). The extension reads { node_id, secret }.
    const bearerAuth = (req: express.Request, res: express.Response) => {
      this.state.lastBearerAuth = req.body;
      const cellId = req.body.cell_id || 'abcd'.repeat(16);
      res.json({
        node_id: 'node_mock_001',
        secret: 'mock_bearer_secret',
        cell_id: cellId,
      });
    };
    this.app.post('/turns/bearer-auth', bearerAuth);
    this.app.post('/api/turns/bearer-auth', bearerAuth);

    // Peer exchange (enliven URI / handoff). The extension reads
    // { permissions, cap_id } (accept) and { certificate_hash } (handoff).
    const peerExchange = (req: express.Request, res: express.Response) => {
      this.state.lastPeerExchange = req.body;
      res.json({
        cap_id: `cap_${Date.now()}`,
        permissions: 'read,write',
        certificate_hash: 'cd'.repeat(32),
      });
    };
    this.app.post('/turns/peer-exchange', peerExchange);
    this.app.post('/api/turns/peer-exchange', peerExchange);

    // Registry: mount a service.
    this.app.post('/registry/mount', (req, res) => {
      this.state.lastMountRequest = req.body;
      const entry = {
        name: req.body.path?.split('/').pop() || 'unnamed',
        path: req.body.path,
        kind: req.body.kind || 'service',
        version: 1,
        tags: req.body.tags || [],
      };
      this.state.services.push(entry);
      res.json({ path: entry.path, version: entry.version, kind: entry.kind });
    });

    // Registry: discover services by tag.
    this.app.get('/registry/discover', (req, res) => {
      const tags = (req.query.tags as string || '').split(',').filter(Boolean);
      let results = this.state.services;
      if (tags.length > 0) {
        results = results.filter(s => tags.some(t => s.tags.includes(t)));
      }
      res.json({ results });
    });

    // Registry: resolve path.
    this.app.get('/registry/resolve/*', (req, res) => {
      const path = '/' + (req.params[0] || '');
      if (path === '/') {
        res.json({ entries: this.state.services });
        return;
      }
      const match = this.state.services.find(s => s.path === path);
      if (match) {
        res.json({ ...match, sturdyRef: `dregg://node_mock_001/${match.name}` });
      } else {
        res.status(404).json({ error: 'Path not found' });
      }
    });

    // Storage: put blob (mandate-gated route on the real node).
    this.app.post('/storage/put', (req, res) => {
      const data = req.body.data || '';
      const hash = `sha256_${Buffer.from(data).toString('hex').slice(0, 16)}`;
      this.state.storedFiles.set(hash, data);
      this.state.quota.bytesStored += data.length;
      this.state.quota.objectCount += 1;
      res.json({ hash, size: data.length });
    });

    // Storage: get blob by hash (mandate-gated; the real node requires the
    // x-dregg-clearance read-compartment header).
    this.app.get('/storage/get/:hash', (req, res) => {
      const content = this.state.storedFiles.get(req.params.hash);
      if (content) {
        res.json({ hash: req.params.hash, data: content, size: content.length });
      } else {
        res.status(404).json({ error: 'Content not found' });
      }
    });

    // Storage: quota (the extension parses the node's snake_case shape).
    this.app.get('/storage/quota', (_req, res) => {
      res.json({
        bytes_stored: this.state.quota.bytesStored,
        bytes_limit: this.state.quota.bytesLimit,
        object_count: this.state.quota.objectCount,
        computrons_used: 0,
        computrons_remaining: this.state.quota.computronsRemaining,
      });
    });

    // Intents: fulfill.
    this.app.post('/intents/fulfill', (req, res) => {
      res.json({
        fulfilled: true,
        intent_id: req.body.intent_id,
        receipt: 'mock_fulfill_receipt',
      });
    });
  }

  async start(): Promise<void> {
    return new Promise((resolve) => {
      this.server = this.app.listen(this.port, () => {
        resolve();
      });
    });
  }

  async stop(): Promise<void> {
    return new Promise((resolve) => {
      if (this.server) {
        // Drop held-open SSE connections so close() can complete.
        this.server.closeAllConnections();
        this.server.close(() => resolve());
      } else {
        resolve();
      }
    });
  }

  reset(): void {
    this.state = this.defaultState();
  }

  get url(): string {
    return `http://localhost:${this.port}`;
  }
}
