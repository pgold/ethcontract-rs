use ethcontract::{
    errors::{ExecutionError, MethodError},
    prelude::*,
};

ethcontract::contract!("examples/truffle/build/contracts/Revert.json");

#[tokio::main]
async fn main() {
    let http = Http::new("http://localhost:8545").unwrap();
    let web3 = Web3::new(http);
    let accounts = web3.eth().accounts().await.unwrap();
    let instance = Revert::builder(&web3)
        .gas(1_000_000u32.into())
        .deploy()
        .await
        .unwrap();
    let result = instance.revert_with_reason().call().await;
    dbg!(&result);
    assert!(matches!(
        result,
        Err(MethodError {
            inner: ExecutionError::Revert(Some("reason".to_string())),
        })
    ));
    dbg!(instance.revert_with_reason().call().await);
    dbg!(instance.revert_without_reason().call().await);
    dbg!(instance.invalid_op_code().call().await);
}
