//! `dregg-private-bazaar-submit` — hand one sealed book to a deployed private
//! Dark Bazaar, out of band.
//!
//! Run it on the deployment host, with the same environment the serving process
//! resolves (`DREGG_PRIVATE_BAZAAR_*`), and pipe the book in on stdin:
//!
//! ```text
//! dregg-private-bazaar-submit <<'BOOK'
//! seed 0xB42AC1
//! bid raider-one=2
//! bid raider-two=3
//! blinding 00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee00c0ffee
//! BOOK
//! ```
//!
//! THE BOOK IS NEVER AN ARGUMENT. A bid limit is a secret and `argv` is legible
//! to every local account through `/proc` and `ps`; the queue's confidentiality
//! boundary is `0600` under the deployment authority directory and this must not
//! widen it. So the document is read from stdin and the buffer is zeroized on the
//! way out.
//!
//! Exit codes: `0` accepted and durable, `1` refused (the reason is printed and
//! nothing was written), `2` the deployment is not configured in this environment.

use std::io::Read;
use std::process::ExitCode;

use zeroize::Zeroize;

use dreggnet_catalog::PrivateBazaarLiveDeployment;
use dreggnet_catalog::private_bazaar_submit::submit_sealed_book_document;

fn main() -> ExitCode {
    let mut document = String::new();
    if let Err(error) = std::io::stdin().read_to_string(&mut document) {
        document.zeroize();
        eprintln!("private submission refused: the book could not be read from stdin: {error}");
        return ExitCode::from(1);
    }

    let deployment = match PrivateBazaarLiveDeployment::from_env() {
        Ok(Some(deployment)) => deployment,
        Ok(None) => {
            document.zeroize();
            eprintln!(
                "private submission refused: no private Bazaar deployment is configured in this \
                 environment (DREGG_PRIVATE_BAZAAR_DEPLOYMENT_ID is unset), so there is no queue \
                 to submit to and no supervisor to drain one"
            );
            return ExitCode::from(2);
        }
        Err(error) => {
            document.zeroize();
            eprintln!("private submission refused: {error}");
            return ExitCode::from(2);
        }
    };

    let outcome = submit_sealed_book_document(&deployment, &document);
    document.zeroize();

    match outcome {
        Ok(accepted) => {
            // Counts only. The seed, the bidders and the limits stay out of the
            // operator's terminal and scrollback.
            println!(
                "accepted at sequence {}; {} submission(s) queued for the supervisor",
                accepted.submission.sequence, accepted.pending
            );
            ExitCode::SUCCESS
        }
        Err(error) => {
            eprintln!("{error}");
            ExitCode::from(1)
        }
    }
}
