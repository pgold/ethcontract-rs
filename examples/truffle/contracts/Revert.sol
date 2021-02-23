pragma solidity ^0.6.0;

contract Revert {
    function revert_with_reason() public pure {
        revert("reason");
    }

    function revert_without_reason() public pure {
        revert();
    }

    function invalid_op_code() public pure {
        assembly {
            invalid()
        }
    }
}
