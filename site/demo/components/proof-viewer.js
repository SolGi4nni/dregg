// Proof Viewer — STARK proof generation, verification, tampering, visualization

export class ProofViewer {
    constructor(wasm) {
        this.wasm = wasm;
        this.currentProofJson = null;
        this.proofData = null;
        this.tampered = false;

        this._bind();
    }

    _bind() {
        document.getElementById('btn-stark-prove').addEventListener('click', () => this._prove());
        document.getElementById('btn-stark-verify').addEventListener('click', () => this._verify());
        document.getElementById('btn-stark-tamper').addEventListener('click', () => this._tamper());
    }

    _prove() {
        const leaf = parseInt(document.getElementById('stark-leaf').value) || 42;
        const depth = parseInt(document.getElementById('stark-depth').value) || 4;

        try {
            const result = this.wasm.generate_demo_stark_proof(leaf, depth);
            this.currentProofJson = result.proof_json;
            this.proofData = result;
            this.tampered = false;

            // Update stats
            document.getElementById('stat-size').textContent = formatBytes(result.proof_size_bytes);
            document.getElementById('stat-prove-time').textContent = result.generation_time_ms.toFixed(1) + 'ms';
            document.getElementById('stat-verify-time').textContent = '--';
            document.getElementById('stat-rows').textContent = result.trace_rows;
            document.getElementById('stat-fri').textContent = result.fri_layers;
            document.getElementById('stat-queries').textContent = result.num_queries;

            // Render proof structure
            this._renderProofViz(result);
            this._renderInspector(result);
        } catch (e) {
            this._showError('Proof generation failed: ' + (e.message || String(e)));
        }
    }

    _verify() {
        if (!this.currentProofJson) {
            this._updateStatus('No proof to verify', 'dim');
            return;
        }

        try {
            const result = this.wasm.verify_demo_stark_proof(this.currentProofJson);
            document.getElementById('stat-verify-time').textContent = result.verification_time_ms.toFixed(1) + 'ms';

            const statusEl = document.getElementById('pi-status');
            if (result.valid) {
                statusEl.innerHTML = '<span class="status-valid">VALID — proof accepted</span>';
            } else {
                statusEl.innerHTML = `<span class="status-invalid">INVALID — ${result.error || 'verification failed'}</span>`;
            }
        } catch (e) {
            this._updateStatus('Verify error: ' + (e.message || String(e)), 'status-invalid');
        }
    }

    _tamper() {
        if (!this.currentProofJson) {
            this._updateStatus('No proof to tamper', 'dim');
            return;
        }

        try {
            this.currentProofJson = this.wasm.tamper_demo_stark_proof(this.currentProofJson);
            this.tampered = true;

            const statusEl = document.getElementById('pi-status');
            statusEl.innerHTML = '<span class="status-tampered">TAMPERED — bits flipped in trace values. Verify to confirm failure.</span>';

            // Update viz to show tampered state
            if (this.proofData) {
                this._renderProofViz(this.proofData, true);
            }
        } catch (e) {
            this._updateStatus('Tamper error: ' + (e.message || String(e)), 'status-invalid');
        }
    }

    _renderProofViz(data, tampered = false) {
        const container = document.getElementById('proof-viz');
        const parsed = JSON.parse(this.currentProofJson);

        container.innerHTML = `
            <div class="proof-structure">
                <div class="proof-layer">
                    <div class="proof-layer-header">
                        <span class="layer-name">Public Inputs</span>
                        <span class="layer-tag public">PUBLIC</span>
                    </div>
                    <div class="proof-layer-body">
                        leaf = ${data.leaf_value}, root = ${data.root_value}
                    </div>
                </div>

                <div class="proof-layer">
                    <div class="proof-layer-header">
                        <span class="layer-name">Trace Commitment</span>
                        <span class="layer-tag private">PRIVATE</span>
                    </div>
                    <div class="proof-layer-body">
                        ${tampered ? '<span style="color:var(--danger)">[TAMPERED]</span> ' : ''}
                        ${data.trace_rows} rows x 6 columns (current, sib0, sib1, sib2, position, parent)
                        <br>commitment: ${parsed.trace_commitment ? parsed.trace_commitment.slice(0, 32) + '...' : 'N/A'}
                    </div>
                </div>

                <div class="proof-layer">
                    <div class="proof-layer-header">
                        <span class="layer-name">FRI Layers (${data.fri_layers})</span>
                        <span class="layer-tag private">PRIVATE</span>
                    </div>
                    <div class="proof-layer-body">
                        ${parsed.fri_commitments ? parsed.fri_commitments.map((c, i) =>
                            `Layer ${i}: ${typeof c === 'string' ? c.slice(0, 24) : JSON.stringify(c).slice(0, 24)}...`
                        ).join('<br>') : 'N/A'}
                    </div>
                </div>

                <div class="proof-layer">
                    <div class="proof-layer-header">
                        <span class="layer-name">Query Proofs (${data.num_queries})</span>
                        <span class="layer-tag public">PUBLIC</span>
                    </div>
                    <div class="proof-layer-body">
                        ${parsed.query_proofs ? parsed.query_proofs.slice(0, 3).map((q, i) =>
                            `Query ${i}: trace_values=[${q.trace_values ? q.trace_values.slice(0, 4).join(', ') + '...' : 'N/A'}]`
                        ).join('<br>') : 'N/A'}
                        ${data.num_queries > 3 ? `<br>... and ${data.num_queries - 3} more` : ''}
                    </div>
                </div>

                <div class="proof-layer">
                    <div class="proof-layer-header">
                        <span class="layer-name">Proof Metadata</span>
                        <span class="layer-tag public">PUBLIC</span>
                    </div>
                    <div class="proof-layer-body">
                        Size: ${formatBytes(data.proof_size_bytes)} | Generated in ${data.generation_time_ms.toFixed(1)}ms
                        <br>Field: BabyBear (p = 2013265921)
                    </div>
                </div>
            </div>
        `;
    }

    _renderInspector(data) {
        const parsed = JSON.parse(this.currentProofJson);

        // Public inputs
        document.getElementById('pi-public').innerHTML = `
            <div class="value-row">
                <span class="value-label">leaf</span>
                <span class="value-data">${data.leaf_value}</span>
            </div>
            <div class="value-row">
                <span class="value-label">root</span>
                <span class="value-data">${data.root_value}</span>
            </div>
        `;

        // Private witness
        document.getElementById('pi-private').innerHTML = `
            <div class="value-row">
                <span class="value-label">rows</span>
                <span class="value-data">${data.trace_rows}</span>
            </div>
            <div class="value-row">
                <span class="value-label">cols</span>
                <span class="value-data">6 (hash, sib0, sib1, sib2, pos, parent)</span>
            </div>
        `;

        // FRI
        const friHtml = parsed.fri_commitments ? parsed.fri_commitments.map((c, i) => `
            <div class="value-row">
                <span class="value-label">L${i}</span>
                <span class="value-data">${typeof c === 'string' ? c.slice(0, 20) + '...' : JSON.stringify(c).slice(0, 20) + '...'}</span>
            </div>
        `).join('') : '<span class="dim">N/A</span>';
        document.getElementById('pi-fri').innerHTML = friHtml;

        // Status
        document.getElementById('pi-status').innerHTML = '<span class="dim">Not verified yet</span>';
    }

    _updateStatus(msg, cls) {
        document.getElementById('pi-status').innerHTML = `<span class="${cls}">${msg}</span>`;
    }

    _showError(msg) {
        document.getElementById('proof-viz').innerHTML = `
            <div class="proof-placeholder">
                <p style="color:var(--danger)">${msg}</p>
            </div>
        `;
    }
}

function formatBytes(bytes) {
    if (bytes < 1024) return bytes + ' B';
    if (bytes < 1024 * 1024) return (bytes / 1024).toFixed(1) + ' KiB';
    return (bytes / (1024 * 1024)).toFixed(1) + ' MiB';
}
