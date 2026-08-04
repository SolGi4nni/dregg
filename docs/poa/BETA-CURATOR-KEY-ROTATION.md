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

## Second explicit beta reset — content counter 3

The counter-2 replacement secret was subsequently found absent from every
durable operator location checked on the local workstation, hbox, persvati,
workhorse, and anchor. The only discovered secret still derived the retired
`0a4d85…e02a52` identity, so it could not honestly authorize counter 3.

On 2026-08-04 the operator explicitly authorized another password-beta
trust-root reset:

- previous public key: `a3e630900af50a8701387c9ab528e3db23a5650c3e1ff3b4b3ee09aa42c65e23`
- replacement public key: `3c757bafe5b819ea7a5d7059630b5fce3725f624fc1d560ff25dfd5059ac7b34`
- first replacement envelope: content epoch 1, counter 3
- persistent secret path:
  `/Users/ember/.local/share/pathofangels/keys/development-curator-v3.key`

The new path is outside the repository, its parent is mode `0700`, and the raw
32-byte seed is mode `0600`. An independent Ed25519 derivation matched the
checked-in public pin before signing. This reset is again an explicitly recorded
development trust-root replacement, not old-key authorization or cryptographic
continuity. The monotonic content counter continues forward; counter 2 is never
reactivated.
