/**
 * Minimal incremental Server-Sent-Events parser for the node's receipt stream
 * (`GET /api/events/stream`, node/src/events.rs).
 *
 * MV3 service workers have no `EventSource`, so the background consumes the
 * stream via `fetch` + `ReadableStream` and feeds the decoded text through
 * this parser. Spec subset implemented: `event:`, `data:` (multi-line, joined
 * with "\n"), `id:`, comment lines (`: hb` keep-alives are dropped), and the
 * blank-line dispatch boundary. CR/CRLF/LF line endings are all accepted.
 */

export interface SseEvent {
  /** The `event:` field (the node sends "receipt"); "message" when absent. */
  event: string;
  /** Joined `data:` payload. */
  data: string;
  /** The `id:` field (the node sends the receipt chain index), if present. */
  id: string | null;
}

export interface SseParser {
  /** Feed a decoded text chunk; returns any events completed by it. */
  feed(chunk: string): SseEvent[];
}

export function createSseParser(): SseParser {
  let buffer = "";
  let eventType = "";
  let dataLines: string[] = [];
  let id: string | null = null;

  function dispatch(out: SseEvent[]): void {
    if (dataLines.length === 0) {
      // Comment-only / heartbeat block: reset type, emit nothing.
      eventType = "";
      return;
    }
    out.push({
      event: eventType || "message",
      data: dataLines.join("\n"),
      id,
    });
    eventType = "";
    dataLines = [];
  }

  function processLine(line: string, out: SseEvent[]): void {
    if (line === "") {
      dispatch(out);
      return;
    }
    if (line.startsWith(":")) return; // comment / keep-alive
    const colon = line.indexOf(":");
    const field = colon === -1 ? line : line.slice(0, colon);
    let value = colon === -1 ? "" : line.slice(colon + 1);
    if (value.startsWith(" ")) value = value.slice(1);
    switch (field) {
      case "event": eventType = value; break;
      case "data": dataLines.push(value); break;
      case "id":
        // Per spec, ids containing NUL are ignored.
        if (!value.includes("\0")) id = value;
        break;
      default: break; // unknown fields (incl. "retry") ignored
    }
  }

  return {
    feed(chunk: string): SseEvent[] {
      buffer += chunk;
      const out: SseEvent[] = [];
      // Split on LF/CRLF/CR; keep the trailing partial line buffered.
      let start = 0;
      for (let i = 0; i < buffer.length; i++) {
        const c = buffer[i];
        if (c === "\n" || c === "\r") {
          processLine(buffer.slice(start, i), out);
          if (c === "\r" && buffer[i + 1] === "\n") i++;
          start = i + 1;
        }
      }
      buffer = buffer.slice(start);
      return out;
    },
  };
}
