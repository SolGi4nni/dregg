# Path of Angels beta curator trust-root reset

Date: 2026-08-04

The protected beta changed its development curator key while preparing content
epoch 1, counter 2.

- retired public key: `0a4d85c84b889408a5cfc98523ca821d3eb1aae2ed6e6331f27b1cb076e02a52`
- replacement public key: `a3e630900af50a8701387c9ab528e3db23a5650c3e1ff3b4b3ee09aa42c65e23`
- first replacement envelope: content epoch 1, counter 2

The first key's development secret was not recoverable from the repository,
operator key store, or the three deployment hosts. It would be dishonest to
describe the replacement as authorized by that key. This is therefore an
explicit beta trust-root reset, not a cryptographically chained rotation.

The replacement secret is persistent operator state outside the repository and
is mode `0600`. Only its public pin is checked in. The content envelope still
binds the exact manifest bytes, federation deployment, content epoch, and
monotonic counter. The HTTPS/basic-auth deployment ceremony replaces the public
pin and signed content atomically; an extension or browser that retained the old
pin must reject until it accepts the new beta trust root.

This reset is acceptable only while Path of Angels is a password-curtained
development beta. Before public release, curator-key changes need a separately
published, reviewable transition policy (for example, an old-key signature,
threshold recovery statement, or an explicitly versioned trust-root ceremony).
