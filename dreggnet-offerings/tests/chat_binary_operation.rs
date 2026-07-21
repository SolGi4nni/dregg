//! Frontend-neutral teeth for the ordinary chat attachment boundary.

use dreggnet_offerings::{
    BinaryOperationDescriptor, ChatBinaryOperationError, MAX_CHAT_BINARY_OPERATION_BYTES,
    preflight_chat_binary_operation,
};

fn descriptor(name: &str, maximum: usize) -> BinaryOperationDescriptor {
    BinaryOperationDescriptor {
        name: name.to_string(),
        title: format!("Apply {name}"),
        input_media_type: format!("application/vnd.dregg.{name}+binary"),
        max_input_bytes: maximum,
        disclosure: "The private producer keeps its witness; the chat transports only the canonical receipt."
            .to_string(),
    }
}

#[test]
fn chat_preflight_selects_the_exact_live_operation_and_closes_the_size_race() {
    let operations = vec![descriptor("preference", 4096), descriptor("quest", 2048)];
    let policy = preflight_chat_binary_operation(&operations, "quest", 1536)
        .expect("the exact live operation is selected before download");

    assert_eq!(policy.descriptor, operations[1]);
    assert_eq!(policy.transport_max_bytes, 2048);
    assert!(policy.validate_body_len(1536).is_ok());
    assert_eq!(
        policy.validate_body_len(1537),
        Err(ChatBinaryOperationError::SizeChanged {
            declared: 1536,
            actual: 1537,
        })
    );
}

#[test]
fn chat_preflight_is_bounded_by_both_the_descriptor_and_the_transport() {
    let descriptor_bound = vec![descriptor("preference", 1024)];
    assert_eq!(
        preflight_chat_binary_operation(&descriptor_bound, "preference", 1025),
        Err(ChatBinaryOperationError::TooLarge {
            actual: 1025,
            maximum: 1024,
        })
    );

    let chat_bound = vec![descriptor("shuffle", usize::MAX)];
    assert_eq!(
        preflight_chat_binary_operation(
            &chat_bound,
            "shuffle",
            MAX_CHAT_BINARY_OPERATION_BYTES + 1,
        ),
        Err(ChatBinaryOperationError::TooLarge {
            actual: MAX_CHAT_BINARY_OPERATION_BYTES + 1,
            maximum: MAX_CHAT_BINARY_OPERATION_BYTES,
        })
    );
}

#[test]
fn unknown_and_ambiguous_chat_routes_fail_before_body_download() {
    let duplicate = vec![descriptor("quest", 1024), descriptor("quest", 2048)];
    assert_eq!(
        preflight_chat_binary_operation(&duplicate, "preference", 0),
        Err(ChatBinaryOperationError::UnknownOperation(
            "preference".to_string()
        ))
    );
    assert_eq!(
        preflight_chat_binary_operation(&duplicate, "quest", 0),
        Err(ChatBinaryOperationError::DuplicateOperation(
            "quest".to_string()
        ))
    );
}
