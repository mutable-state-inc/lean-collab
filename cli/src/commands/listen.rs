//! Listen to Ensue SSE stream, output events as JSON lines

use anyhow::Result;
use eventsource_client::Client;
use futures::StreamExt;

use crate::config::load_config;
use crate::ensue::DEFAULT_SSE_URL;

pub async fn run(prefix: Option<&str>) -> Result<()> {
    let config = load_config()?;
    let filter_prefix = prefix.unwrap_or(&config.theorem_id);

    // Build SSE URL
    let sse_url = DEFAULT_SSE_URL;

    eprintln!("Connecting to {} ...", sse_url);
    eprintln!("Filtering for prefix: {}", filter_prefix);

    // Create SSE client
    let client = eventsource_client::ClientBuilder::for_url(sse_url)?
        .header("Authorization", &format!("Bearer {}", config.ensue_api_key))?
        .build();

    // Process events
    let mut stream = client.stream();

    while let Some(event) = stream.next().await {
        match event {
            Ok(eventsource_client::SSE::Event(ev)) => {
                // Parse the event data
                let data = ev.data;

                // Filter by prefix - check if the URI contains our prefix
                // Events have format: {"method":"notifications/resources/updated","params":{"uri":"memory:///proofs/..."}}
                if let Ok(json) = serde_json::from_str::<serde_json::Value>(&data) {
                    let uri = json
                        .get("params")
                        .and_then(|p| p.get("uri"))
                        .and_then(|u| u.as_str())
                        .unwrap_or("");

                    // Check if URI matches our filter prefix
                    if uri.contains(filter_prefix) {
                        // Output as JSON line to stdout
                        println!("{}", data);
                    }
                }
            }
            Ok(eventsource_client::SSE::Comment(_)) => {
                // Ignore comments (keep-alive)
            }
            Err(e) => {
                eprintln!("SSE error: {}", e);
                // Continue on errors, will reconnect
            }
        }
    }

    Ok(())
}
