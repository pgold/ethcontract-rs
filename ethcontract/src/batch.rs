//! Module containing components to batch multiple contract calls
//! into a single request to the Node.

use futures::channel::oneshot::{channel, Sender};
use web3::{
    error::Error as Web3Error,
    helpers::{self},
    types::{BlockId, BlockNumber, Bytes, CallRequest},
    BatchTransport as Web3BatchTransport,
};

/// Struct allowing to batch multiple calls into a single Node request
pub struct CallBatch<T: Web3BatchTransport> {
    inner: T,
    requests: Vec<(Request, CompletionHandler)>,
}

type Request = (CallRequest, Option<BlockId>);
type CompletionHandler = Sender<Result<Bytes, Web3Error>>;

impl<T: Web3BatchTransport> CallBatch<T> {
    /// Create a new instance from a BatchTransport
    pub fn new(inner: T) -> Self {
        Self {
            inner,
            requests: Default::default(),
        }
    }

    /// Adds a call request to the current batch. The resulting future can only resolve after
    /// the batch has been resolved via `execute_all`.
    /// Explicitly returns a Future instead of being declared `async` so that we can split the
    /// logic into a synchronous and asynchronous section and don't want to capture `&mut self`
    /// in the future.
    /// Panics, if the batch is dropped before executing.
    pub fn push(
        &mut self,
        call: CallRequest,
        block: Option<BlockId>,
    ) -> impl std::future::Future<Output = Result<Bytes, Web3Error>> {
        let (tx, rx) = channel();
        self.requests.push(((call, block), tx));
        async move {
            rx.await.unwrap_or_else(|_| {
                Err(Web3Error::Transport(
                    "Batch has been dropped without executing".to_owned(),
                ))
            })
        }
    }

    /// Execute and resolve all enqueued CallRequests in a single RPC call
    pub async fn execute_all(self) -> Result<(), Web3Error> {
        let results = self
            .inner
            .send_batch(self.requests.iter().map(|((request, block), _)| {
                let req = helpers::serialize(request);
                let block =
                    helpers::serialize(&block.unwrap_or_else(|| BlockNumber::Latest.into()));
                let (id, request) = self.inner.prepare("eth_call", vec![req, block]);
                (id, request)
            }))
            .await?;
        for (result, (_, sender)) in results.into_iter().zip(self.requests.into_iter()) {
            let _ = sender.send(result.and_then(helpers::decode));
        }
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use futures::future::join_all;
    use serde_json::json;

    use super::*;
    use crate::test::prelude::FutureTestExt;
    use crate::test::transport::TestTransport;

    #[test]
    fn batches_calls() {
        let mut transport = TestTransport::new();
        transport.add_response(json!([json!("0x01"), json!("0x02")]));

        let mut batch = CallBatch::new(transport);

        let results = vec![
            batch.push(CallRequest::default(), None),
            batch.push(CallRequest::default(), None),
        ];

        batch.execute_all().immediate().unwrap();

        let results = join_all(results).immediate();
        assert_eq!(results[0].clone().unwrap().0, vec![1u8]);
        assert_eq!(results[1].clone().unwrap().0, vec![2u8]);
    }

    #[test]
    fn resolves_calls_to_error_if_dropped() {
        let future = {
            let transport = TestTransport::new();
            let mut batch = CallBatch::new(transport);
            batch.push(CallRequest::default(), None)
        };

        assert!(matches!(
            future.immediate().unwrap_err(),
            Web3Error::Transport(_)
        ));
    }
}