// Sources flattened with hardhat v2.9.7 https://hardhat.org

// File @openzeppelin/contracts/token/ERC20/IERC20.sol

// SPDX-License-Identifier: MIT
// OpenZeppelin Contracts (last updated v4.6.0) (token/ERC20/IERC20.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}


// File @openzeppelin/contracts/token/ERC20/extensions/draft-IERC20Permit.sol

// OpenZeppelin Contracts v4.4.1 (token/ERC20/extensions/draft-IERC20Permit.sol)

pragma solidity ^0.8.0;

/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}


// File @openzeppelin/contracts/utils/Address.sol

// OpenZeppelin Contracts (last updated v4.8.0) (utils/Address.sol)

pragma solidity ^0.8.1;

/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://diligence.consensys.net/posts/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.5.11/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}


// File @openzeppelin/contracts/token/ERC20/utils/SafeERC20.sol

// OpenZeppelin Contracts (last updated v4.8.0) (token/ERC20/utils/SafeERC20.sol)

pragma solidity ^0.8.0;



/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    function safeTransfer(
        IERC20 token,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    function safeTransferFrom(
        IERC20 token,
        address from,
        address to,
        uint256 value
    ) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    function safeIncreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        uint256 newAllowance = token.allowance(address(this), spender) + value;
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
    }

    function safeDecreaseAllowance(
        IERC20 token,
        address spender,
        uint256 value
    ) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            uint256 newAllowance = oldAllowance - value;
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, newAllowance));
        }
    }

    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        if (returndata.length > 0) {
            // Return data is optional
            require(abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
        }
    }
}


// File @openzeppelin/contracts/utils/math/SafeCast.sol

// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/SafeCast.sol)
// This file was procedurally generated from scripts/generate/templates/SafeCast.js.

pragma solidity ^0.8.0;

/**
 * @dev Wrappers over Solidity's uintXX/intXX casting operators with added overflow
 * checks.
 *
 * Downcasting from uint256/int256 in Solidity does not revert on overflow. This can
 * easily result in undesired exploitation or bugs, since developers usually
 * assume that overflows raise errors. `SafeCast` restores this intuition by
 * reverting the transaction when such an operation overflows.
 *
 * Using this library instead of the unchecked operations eliminates an entire
 * class of bugs, so it's recommended to use it always.
 *
 * Can be combined with {SafeMath} and {SignedSafeMath} to extend it to smaller types, by performing
 * all math on `uint256` and `int256` and then downcasting.
 */
library SafeCast {
    /**
     * @dev Returns the downcasted uint248 from uint256, reverting on
     * overflow (when the input is greater than largest uint248).
     *
     * Counterpart to Solidity's `uint248` operator.
     *
     * Requirements:
     *
     * - input must fit into 248 bits
     *
     * _Available since v4.7._
     */
    function toUint248(uint256 value) internal pure returns (uint248) {
        require(value <= type(uint248).max, "SafeCast: value doesn't fit in 248 bits");
        return uint248(value);
    }

    /**
     * @dev Returns the downcasted uint240 from uint256, reverting on
     * overflow (when the input is greater than largest uint240).
     *
     * Counterpart to Solidity's `uint240` operator.
     *
     * Requirements:
     *
     * - input must fit into 240 bits
     *
     * _Available since v4.7._
     */
    function toUint240(uint256 value) internal pure returns (uint240) {
        require(value <= type(uint240).max, "SafeCast: value doesn't fit in 240 bits");
        return uint240(value);
    }

    /**
     * @dev Returns the downcasted uint232 from uint256, reverting on
     * overflow (when the input is greater than largest uint232).
     *
     * Counterpart to Solidity's `uint232` operator.
     *
     * Requirements:
     *
     * - input must fit into 232 bits
     *
     * _Available since v4.7._
     */
    function toUint232(uint256 value) internal pure returns (uint232) {
        require(value <= type(uint232).max, "SafeCast: value doesn't fit in 232 bits");
        return uint232(value);
    }

    /**
     * @dev Returns the downcasted uint224 from uint256, reverting on
     * overflow (when the input is greater than largest uint224).
     *
     * Counterpart to Solidity's `uint224` operator.
     *
     * Requirements:
     *
     * - input must fit into 224 bits
     *
     * _Available since v4.2._
     */
    function toUint224(uint256 value) internal pure returns (uint224) {
        require(value <= type(uint224).max, "SafeCast: value doesn't fit in 224 bits");
        return uint224(value);
    }

    /**
     * @dev Returns the downcasted uint216 from uint256, reverting on
     * overflow (when the input is greater than largest uint216).
     *
     * Counterpart to Solidity's `uint216` operator.
     *
     * Requirements:
     *
     * - input must fit into 216 bits
     *
     * _Available since v4.7._
     */
    function toUint216(uint256 value) internal pure returns (uint216) {
        require(value <= type(uint216).max, "SafeCast: value doesn't fit in 216 bits");
        return uint216(value);
    }

    /**
     * @dev Returns the downcasted uint208 from uint256, reverting on
     * overflow (when the input is greater than largest uint208).
     *
     * Counterpart to Solidity's `uint208` operator.
     *
     * Requirements:
     *
     * - input must fit into 208 bits
     *
     * _Available since v4.7._
     */
    function toUint208(uint256 value) internal pure returns (uint208) {
        require(value <= type(uint208).max, "SafeCast: value doesn't fit in 208 bits");
        return uint208(value);
    }

    /**
     * @dev Returns the downcasted uint200 from uint256, reverting on
     * overflow (when the input is greater than largest uint200).
     *
     * Counterpart to Solidity's `uint200` operator.
     *
     * Requirements:
     *
     * - input must fit into 200 bits
     *
     * _Available since v4.7._
     */
    function toUint200(uint256 value) internal pure returns (uint200) {
        require(value <= type(uint200).max, "SafeCast: value doesn't fit in 200 bits");
        return uint200(value);
    }

    /**
     * @dev Returns the downcasted uint192 from uint256, reverting on
     * overflow (when the input is greater than largest uint192).
     *
     * Counterpart to Solidity's `uint192` operator.
     *
     * Requirements:
     *
     * - input must fit into 192 bits
     *
     * _Available since v4.7._
     */
    function toUint192(uint256 value) internal pure returns (uint192) {
        require(value <= type(uint192).max, "SafeCast: value doesn't fit in 192 bits");
        return uint192(value);
    }

    /**
     * @dev Returns the downcasted uint184 from uint256, reverting on
     * overflow (when the input is greater than largest uint184).
     *
     * Counterpart to Solidity's `uint184` operator.
     *
     * Requirements:
     *
     * - input must fit into 184 bits
     *
     * _Available since v4.7._
     */
    function toUint184(uint256 value) internal pure returns (uint184) {
        require(value <= type(uint184).max, "SafeCast: value doesn't fit in 184 bits");
        return uint184(value);
    }

    /**
     * @dev Returns the downcasted uint176 from uint256, reverting on
     * overflow (when the input is greater than largest uint176).
     *
     * Counterpart to Solidity's `uint176` operator.
     *
     * Requirements:
     *
     * - input must fit into 176 bits
     *
     * _Available since v4.7._
     */
    function toUint176(uint256 value) internal pure returns (uint176) {
        require(value <= type(uint176).max, "SafeCast: value doesn't fit in 176 bits");
        return uint176(value);
    }

    /**
     * @dev Returns the downcasted uint168 from uint256, reverting on
     * overflow (when the input is greater than largest uint168).
     *
     * Counterpart to Solidity's `uint168` operator.
     *
     * Requirements:
     *
     * - input must fit into 168 bits
     *
     * _Available since v4.7._
     */
    function toUint168(uint256 value) internal pure returns (uint168) {
        require(value <= type(uint168).max, "SafeCast: value doesn't fit in 168 bits");
        return uint168(value);
    }

    /**
     * @dev Returns the downcasted uint160 from uint256, reverting on
     * overflow (when the input is greater than largest uint160).
     *
     * Counterpart to Solidity's `uint160` operator.
     *
     * Requirements:
     *
     * - input must fit into 160 bits
     *
     * _Available since v4.7._
     */
    function toUint160(uint256 value) internal pure returns (uint160) {
        require(value <= type(uint160).max, "SafeCast: value doesn't fit in 160 bits");
        return uint160(value);
    }

    /**
     * @dev Returns the downcasted uint152 from uint256, reverting on
     * overflow (when the input is greater than largest uint152).
     *
     * Counterpart to Solidity's `uint152` operator.
     *
     * Requirements:
     *
     * - input must fit into 152 bits
     *
     * _Available since v4.7._
     */
    function toUint152(uint256 value) internal pure returns (uint152) {
        require(value <= type(uint152).max, "SafeCast: value doesn't fit in 152 bits");
        return uint152(value);
    }

    /**
     * @dev Returns the downcasted uint144 from uint256, reverting on
     * overflow (when the input is greater than largest uint144).
     *
     * Counterpart to Solidity's `uint144` operator.
     *
     * Requirements:
     *
     * - input must fit into 144 bits
     *
     * _Available since v4.7._
     */
    function toUint144(uint256 value) internal pure returns (uint144) {
        require(value <= type(uint144).max, "SafeCast: value doesn't fit in 144 bits");
        return uint144(value);
    }

    /**
     * @dev Returns the downcasted uint136 from uint256, reverting on
     * overflow (when the input is greater than largest uint136).
     *
     * Counterpart to Solidity's `uint136` operator.
     *
     * Requirements:
     *
     * - input must fit into 136 bits
     *
     * _Available since v4.7._
     */
    function toUint136(uint256 value) internal pure returns (uint136) {
        require(value <= type(uint136).max, "SafeCast: value doesn't fit in 136 bits");
        return uint136(value);
    }

    /**
     * @dev Returns the downcasted uint128 from uint256, reverting on
     * overflow (when the input is greater than largest uint128).
     *
     * Counterpart to Solidity's `uint128` operator.
     *
     * Requirements:
     *
     * - input must fit into 128 bits
     *
     * _Available since v2.5._
     */
    function toUint128(uint256 value) internal pure returns (uint128) {
        require(value <= type(uint128).max, "SafeCast: value doesn't fit in 128 bits");
        return uint128(value);
    }

    /**
     * @dev Returns the downcasted uint120 from uint256, reverting on
     * overflow (when the input is greater than largest uint120).
     *
     * Counterpart to Solidity's `uint120` operator.
     *
     * Requirements:
     *
     * - input must fit into 120 bits
     *
     * _Available since v4.7._
     */
    function toUint120(uint256 value) internal pure returns (uint120) {
        require(value <= type(uint120).max, "SafeCast: value doesn't fit in 120 bits");
        return uint120(value);
    }

    /**
     * @dev Returns the downcasted uint112 from uint256, reverting on
     * overflow (when the input is greater than largest uint112).
     *
     * Counterpart to Solidity's `uint112` operator.
     *
     * Requirements:
     *
     * - input must fit into 112 bits
     *
     * _Available since v4.7._
     */
    function toUint112(uint256 value) internal pure returns (uint112) {
        require(value <= type(uint112).max, "SafeCast: value doesn't fit in 112 bits");
        return uint112(value);
    }

    /**
     * @dev Returns the downcasted uint104 from uint256, reverting on
     * overflow (when the input is greater than largest uint104).
     *
     * Counterpart to Solidity's `uint104` operator.
     *
     * Requirements:
     *
     * - input must fit into 104 bits
     *
     * _Available since v4.7._
     */
    function toUint104(uint256 value) internal pure returns (uint104) {
        require(value <= type(uint104).max, "SafeCast: value doesn't fit in 104 bits");
        return uint104(value);
    }

    /**
     * @dev Returns the downcasted uint96 from uint256, reverting on
     * overflow (when the input is greater than largest uint96).
     *
     * Counterpart to Solidity's `uint96` operator.
     *
     * Requirements:
     *
     * - input must fit into 96 bits
     *
     * _Available since v4.2._
     */
    function toUint96(uint256 value) internal pure returns (uint96) {
        require(value <= type(uint96).max, "SafeCast: value doesn't fit in 96 bits");
        return uint96(value);
    }

    /**
     * @dev Returns the downcasted uint88 from uint256, reverting on
     * overflow (when the input is greater than largest uint88).
     *
     * Counterpart to Solidity's `uint88` operator.
     *
     * Requirements:
     *
     * - input must fit into 88 bits
     *
     * _Available since v4.7._
     */
    function toUint88(uint256 value) internal pure returns (uint88) {
        require(value <= type(uint88).max, "SafeCast: value doesn't fit in 88 bits");
        return uint88(value);
    }

    /**
     * @dev Returns the downcasted uint80 from uint256, reverting on
     * overflow (when the input is greater than largest uint80).
     *
     * Counterpart to Solidity's `uint80` operator.
     *
     * Requirements:
     *
     * - input must fit into 80 bits
     *
     * _Available since v4.7._
     */
    function toUint80(uint256 value) internal pure returns (uint80) {
        require(value <= type(uint80).max, "SafeCast: value doesn't fit in 80 bits");
        return uint80(value);
    }

    /**
     * @dev Returns the downcasted uint72 from uint256, reverting on
     * overflow (when the input is greater than largest uint72).
     *
     * Counterpart to Solidity's `uint72` operator.
     *
     * Requirements:
     *
     * - input must fit into 72 bits
     *
     * _Available since v4.7._
     */
    function toUint72(uint256 value) internal pure returns (uint72) {
        require(value <= type(uint72).max, "SafeCast: value doesn't fit in 72 bits");
        return uint72(value);
    }

    /**
     * @dev Returns the downcasted uint64 from uint256, reverting on
     * overflow (when the input is greater than largest uint64).
     *
     * Counterpart to Solidity's `uint64` operator.
     *
     * Requirements:
     *
     * - input must fit into 64 bits
     *
     * _Available since v2.5._
     */
    function toUint64(uint256 value) internal pure returns (uint64) {
        require(value <= type(uint64).max, "SafeCast: value doesn't fit in 64 bits");
        return uint64(value);
    }

    /**
     * @dev Returns the downcasted uint56 from uint256, reverting on
     * overflow (when the input is greater than largest uint56).
     *
     * Counterpart to Solidity's `uint56` operator.
     *
     * Requirements:
     *
     * - input must fit into 56 bits
     *
     * _Available since v4.7._
     */
    function toUint56(uint256 value) internal pure returns (uint56) {
        require(value <= type(uint56).max, "SafeCast: value doesn't fit in 56 bits");
        return uint56(value);
    }

    /**
     * @dev Returns the downcasted uint48 from uint256, reverting on
     * overflow (when the input is greater than largest uint48).
     *
     * Counterpart to Solidity's `uint48` operator.
     *
     * Requirements:
     *
     * - input must fit into 48 bits
     *
     * _Available since v4.7._
     */
    function toUint48(uint256 value) internal pure returns (uint48) {
        require(value <= type(uint48).max, "SafeCast: value doesn't fit in 48 bits");
        return uint48(value);
    }

    /**
     * @dev Returns the downcasted uint40 from uint256, reverting on
     * overflow (when the input is greater than largest uint40).
     *
     * Counterpart to Solidity's `uint40` operator.
     *
     * Requirements:
     *
     * - input must fit into 40 bits
     *
     * _Available since v4.7._
     */
    function toUint40(uint256 value) internal pure returns (uint40) {
        require(value <= type(uint40).max, "SafeCast: value doesn't fit in 40 bits");
        return uint40(value);
    }

    /**
     * @dev Returns the downcasted uint32 from uint256, reverting on
     * overflow (when the input is greater than largest uint32).
     *
     * Counterpart to Solidity's `uint32` operator.
     *
     * Requirements:
     *
     * - input must fit into 32 bits
     *
     * _Available since v2.5._
     */
    function toUint32(uint256 value) internal pure returns (uint32) {
        require(value <= type(uint32).max, "SafeCast: value doesn't fit in 32 bits");
        return uint32(value);
    }

    /**
     * @dev Returns the downcasted uint24 from uint256, reverting on
     * overflow (when the input is greater than largest uint24).
     *
     * Counterpart to Solidity's `uint24` operator.
     *
     * Requirements:
     *
     * - input must fit into 24 bits
     *
     * _Available since v4.7._
     */
    function toUint24(uint256 value) internal pure returns (uint24) {
        require(value <= type(uint24).max, "SafeCast: value doesn't fit in 24 bits");
        return uint24(value);
    }

    /**
     * @dev Returns the downcasted uint16 from uint256, reverting on
     * overflow (when the input is greater than largest uint16).
     *
     * Counterpart to Solidity's `uint16` operator.
     *
     * Requirements:
     *
     * - input must fit into 16 bits
     *
     * _Available since v2.5._
     */
    function toUint16(uint256 value) internal pure returns (uint16) {
        require(value <= type(uint16).max, "SafeCast: value doesn't fit in 16 bits");
        return uint16(value);
    }

    /**
     * @dev Returns the downcasted uint8 from uint256, reverting on
     * overflow (when the input is greater than largest uint8).
     *
     * Counterpart to Solidity's `uint8` operator.
     *
     * Requirements:
     *
     * - input must fit into 8 bits
     *
     * _Available since v2.5._
     */
    function toUint8(uint256 value) internal pure returns (uint8) {
        require(value <= type(uint8).max, "SafeCast: value doesn't fit in 8 bits");
        return uint8(value);
    }

    /**
     * @dev Converts a signed int256 into an unsigned uint256.
     *
     * Requirements:
     *
     * - input must be greater than or equal to 0.
     *
     * _Available since v3.0._
     */
    function toUint256(int256 value) internal pure returns (uint256) {
        require(value >= 0, "SafeCast: value must be positive");
        return uint256(value);
    }

    /**
     * @dev Returns the downcasted int248 from int256, reverting on
     * overflow (when the input is less than smallest int248 or
     * greater than largest int248).
     *
     * Counterpart to Solidity's `int248` operator.
     *
     * Requirements:
     *
     * - input must fit into 248 bits
     *
     * _Available since v4.7._
     */
    function toInt248(int256 value) internal pure returns (int248 downcasted) {
        downcasted = int248(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 248 bits");
    }

    /**
     * @dev Returns the downcasted int240 from int256, reverting on
     * overflow (when the input is less than smallest int240 or
     * greater than largest int240).
     *
     * Counterpart to Solidity's `int240` operator.
     *
     * Requirements:
     *
     * - input must fit into 240 bits
     *
     * _Available since v4.7._
     */
    function toInt240(int256 value) internal pure returns (int240 downcasted) {
        downcasted = int240(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 240 bits");
    }

    /**
     * @dev Returns the downcasted int232 from int256, reverting on
     * overflow (when the input is less than smallest int232 or
     * greater than largest int232).
     *
     * Counterpart to Solidity's `int232` operator.
     *
     * Requirements:
     *
     * - input must fit into 232 bits
     *
     * _Available since v4.7._
     */
    function toInt232(int256 value) internal pure returns (int232 downcasted) {
        downcasted = int232(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 232 bits");
    }

    /**
     * @dev Returns the downcasted int224 from int256, reverting on
     * overflow (when the input is less than smallest int224 or
     * greater than largest int224).
     *
     * Counterpart to Solidity's `int224` operator.
     *
     * Requirements:
     *
     * - input must fit into 224 bits
     *
     * _Available since v4.7._
     */
    function toInt224(int256 value) internal pure returns (int224 downcasted) {
        downcasted = int224(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 224 bits");
    }

    /**
     * @dev Returns the downcasted int216 from int256, reverting on
     * overflow (when the input is less than smallest int216 or
     * greater than largest int216).
     *
     * Counterpart to Solidity's `int216` operator.
     *
     * Requirements:
     *
     * - input must fit into 216 bits
     *
     * _Available since v4.7._
     */
    function toInt216(int256 value) internal pure returns (int216 downcasted) {
        downcasted = int216(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 216 bits");
    }

    /**
     * @dev Returns the downcasted int208 from int256, reverting on
     * overflow (when the input is less than smallest int208 or
     * greater than largest int208).
     *
     * Counterpart to Solidity's `int208` operator.
     *
     * Requirements:
     *
     * - input must fit into 208 bits
     *
     * _Available since v4.7._
     */
    function toInt208(int256 value) internal pure returns (int208 downcasted) {
        downcasted = int208(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 208 bits");
    }

    /**
     * @dev Returns the downcasted int200 from int256, reverting on
     * overflow (when the input is less than smallest int200 or
     * greater than largest int200).
     *
     * Counterpart to Solidity's `int200` operator.
     *
     * Requirements:
     *
     * - input must fit into 200 bits
     *
     * _Available since v4.7._
     */
    function toInt200(int256 value) internal pure returns (int200 downcasted) {
        downcasted = int200(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 200 bits");
    }

    /**
     * @dev Returns the downcasted int192 from int256, reverting on
     * overflow (when the input is less than smallest int192 or
     * greater than largest int192).
     *
     * Counterpart to Solidity's `int192` operator.
     *
     * Requirements:
     *
     * - input must fit into 192 bits
     *
     * _Available since v4.7._
     */
    function toInt192(int256 value) internal pure returns (int192 downcasted) {
        downcasted = int192(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 192 bits");
    }

    /**
     * @dev Returns the downcasted int184 from int256, reverting on
     * overflow (when the input is less than smallest int184 or
     * greater than largest int184).
     *
     * Counterpart to Solidity's `int184` operator.
     *
     * Requirements:
     *
     * - input must fit into 184 bits
     *
     * _Available since v4.7._
     */
    function toInt184(int256 value) internal pure returns (int184 downcasted) {
        downcasted = int184(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 184 bits");
    }

    /**
     * @dev Returns the downcasted int176 from int256, reverting on
     * overflow (when the input is less than smallest int176 or
     * greater than largest int176).
     *
     * Counterpart to Solidity's `int176` operator.
     *
     * Requirements:
     *
     * - input must fit into 176 bits
     *
     * _Available since v4.7._
     */
    function toInt176(int256 value) internal pure returns (int176 downcasted) {
        downcasted = int176(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 176 bits");
    }

    /**
     * @dev Returns the downcasted int168 from int256, reverting on
     * overflow (when the input is less than smallest int168 or
     * greater than largest int168).
     *
     * Counterpart to Solidity's `int168` operator.
     *
     * Requirements:
     *
     * - input must fit into 168 bits
     *
     * _Available since v4.7._
     */
    function toInt168(int256 value) internal pure returns (int168 downcasted) {
        downcasted = int168(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 168 bits");
    }

    /**
     * @dev Returns the downcasted int160 from int256, reverting on
     * overflow (when the input is less than smallest int160 or
     * greater than largest int160).
     *
     * Counterpart to Solidity's `int160` operator.
     *
     * Requirements:
     *
     * - input must fit into 160 bits
     *
     * _Available since v4.7._
     */
    function toInt160(int256 value) internal pure returns (int160 downcasted) {
        downcasted = int160(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 160 bits");
    }

    /**
     * @dev Returns the downcasted int152 from int256, reverting on
     * overflow (when the input is less than smallest int152 or
     * greater than largest int152).
     *
     * Counterpart to Solidity's `int152` operator.
     *
     * Requirements:
     *
     * - input must fit into 152 bits
     *
     * _Available since v4.7._
     */
    function toInt152(int256 value) internal pure returns (int152 downcasted) {
        downcasted = int152(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 152 bits");
    }

    /**
     * @dev Returns the downcasted int144 from int256, reverting on
     * overflow (when the input is less than smallest int144 or
     * greater than largest int144).
     *
     * Counterpart to Solidity's `int144` operator.
     *
     * Requirements:
     *
     * - input must fit into 144 bits
     *
     * _Available since v4.7._
     */
    function toInt144(int256 value) internal pure returns (int144 downcasted) {
        downcasted = int144(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 144 bits");
    }

    /**
     * @dev Returns the downcasted int136 from int256, reverting on
     * overflow (when the input is less than smallest int136 or
     * greater than largest int136).
     *
     * Counterpart to Solidity's `int136` operator.
     *
     * Requirements:
     *
     * - input must fit into 136 bits
     *
     * _Available since v4.7._
     */
    function toInt136(int256 value) internal pure returns (int136 downcasted) {
        downcasted = int136(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 136 bits");
    }

    /**
     * @dev Returns the downcasted int128 from int256, reverting on
     * overflow (when the input is less than smallest int128 or
     * greater than largest int128).
     *
     * Counterpart to Solidity's `int128` operator.
     *
     * Requirements:
     *
     * - input must fit into 128 bits
     *
     * _Available since v3.1._
     */
    function toInt128(int256 value) internal pure returns (int128 downcasted) {
        downcasted = int128(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 128 bits");
    }

    /**
     * @dev Returns the downcasted int120 from int256, reverting on
     * overflow (when the input is less than smallest int120 or
     * greater than largest int120).
     *
     * Counterpart to Solidity's `int120` operator.
     *
     * Requirements:
     *
     * - input must fit into 120 bits
     *
     * _Available since v4.7._
     */
    function toInt120(int256 value) internal pure returns (int120 downcasted) {
        downcasted = int120(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 120 bits");
    }

    /**
     * @dev Returns the downcasted int112 from int256, reverting on
     * overflow (when the input is less than smallest int112 or
     * greater than largest int112).
     *
     * Counterpart to Solidity's `int112` operator.
     *
     * Requirements:
     *
     * - input must fit into 112 bits
     *
     * _Available since v4.7._
     */
    function toInt112(int256 value) internal pure returns (int112 downcasted) {
        downcasted = int112(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 112 bits");
    }

    /**
     * @dev Returns the downcasted int104 from int256, reverting on
     * overflow (when the input is less than smallest int104 or
     * greater than largest int104).
     *
     * Counterpart to Solidity's `int104` operator.
     *
     * Requirements:
     *
     * - input must fit into 104 bits
     *
     * _Available since v4.7._
     */
    function toInt104(int256 value) internal pure returns (int104 downcasted) {
        downcasted = int104(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 104 bits");
    }

    /**
     * @dev Returns the downcasted int96 from int256, reverting on
     * overflow (when the input is less than smallest int96 or
     * greater than largest int96).
     *
     * Counterpart to Solidity's `int96` operator.
     *
     * Requirements:
     *
     * - input must fit into 96 bits
     *
     * _Available since v4.7._
     */
    function toInt96(int256 value) internal pure returns (int96 downcasted) {
        downcasted = int96(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 96 bits");
    }

    /**
     * @dev Returns the downcasted int88 from int256, reverting on
     * overflow (when the input is less than smallest int88 or
     * greater than largest int88).
     *
     * Counterpart to Solidity's `int88` operator.
     *
     * Requirements:
     *
     * - input must fit into 88 bits
     *
     * _Available since v4.7._
     */
    function toInt88(int256 value) internal pure returns (int88 downcasted) {
        downcasted = int88(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 88 bits");
    }

    /**
     * @dev Returns the downcasted int80 from int256, reverting on
     * overflow (when the input is less than smallest int80 or
     * greater than largest int80).
     *
     * Counterpart to Solidity's `int80` operator.
     *
     * Requirements:
     *
     * - input must fit into 80 bits
     *
     * _Available since v4.7._
     */
    function toInt80(int256 value) internal pure returns (int80 downcasted) {
        downcasted = int80(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 80 bits");
    }

    /**
     * @dev Returns the downcasted int72 from int256, reverting on
     * overflow (when the input is less than smallest int72 or
     * greater than largest int72).
     *
     * Counterpart to Solidity's `int72` operator.
     *
     * Requirements:
     *
     * - input must fit into 72 bits
     *
     * _Available since v4.7._
     */
    function toInt72(int256 value) internal pure returns (int72 downcasted) {
        downcasted = int72(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 72 bits");
    }

    /**
     * @dev Returns the downcasted int64 from int256, reverting on
     * overflow (when the input is less than smallest int64 or
     * greater than largest int64).
     *
     * Counterpart to Solidity's `int64` operator.
     *
     * Requirements:
     *
     * - input must fit into 64 bits
     *
     * _Available since v3.1._
     */
    function toInt64(int256 value) internal pure returns (int64 downcasted) {
        downcasted = int64(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 64 bits");
    }

    /**
     * @dev Returns the downcasted int56 from int256, reverting on
     * overflow (when the input is less than smallest int56 or
     * greater than largest int56).
     *
     * Counterpart to Solidity's `int56` operator.
     *
     * Requirements:
     *
     * - input must fit into 56 bits
     *
     * _Available since v4.7._
     */
    function toInt56(int256 value) internal pure returns (int56 downcasted) {
        downcasted = int56(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 56 bits");
    }

    /**
     * @dev Returns the downcasted int48 from int256, reverting on
     * overflow (when the input is less than smallest int48 or
     * greater than largest int48).
     *
     * Counterpart to Solidity's `int48` operator.
     *
     * Requirements:
     *
     * - input must fit into 48 bits
     *
     * _Available since v4.7._
     */
    function toInt48(int256 value) internal pure returns (int48 downcasted) {
        downcasted = int48(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 48 bits");
    }

    /**
     * @dev Returns the downcasted int40 from int256, reverting on
     * overflow (when the input is less than smallest int40 or
     * greater than largest int40).
     *
     * Counterpart to Solidity's `int40` operator.
     *
     * Requirements:
     *
     * - input must fit into 40 bits
     *
     * _Available since v4.7._
     */
    function toInt40(int256 value) internal pure returns (int40 downcasted) {
        downcasted = int40(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 40 bits");
    }

    /**
     * @dev Returns the downcasted int32 from int256, reverting on
     * overflow (when the input is less than smallest int32 or
     * greater than largest int32).
     *
     * Counterpart to Solidity's `int32` operator.
     *
     * Requirements:
     *
     * - input must fit into 32 bits
     *
     * _Available since v3.1._
     */
    function toInt32(int256 value) internal pure returns (int32 downcasted) {
        downcasted = int32(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 32 bits");
    }

    /**
     * @dev Returns the downcasted int24 from int256, reverting on
     * overflow (when the input is less than smallest int24 or
     * greater than largest int24).
     *
     * Counterpart to Solidity's `int24` operator.
     *
     * Requirements:
     *
     * - input must fit into 24 bits
     *
     * _Available since v4.7._
     */
    function toInt24(int256 value) internal pure returns (int24 downcasted) {
        downcasted = int24(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 24 bits");
    }

    /**
     * @dev Returns the downcasted int16 from int256, reverting on
     * overflow (when the input is less than smallest int16 or
     * greater than largest int16).
     *
     * Counterpart to Solidity's `int16` operator.
     *
     * Requirements:
     *
     * - input must fit into 16 bits
     *
     * _Available since v3.1._
     */
    function toInt16(int256 value) internal pure returns (int16 downcasted) {
        downcasted = int16(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 16 bits");
    }

    /**
     * @dev Returns the downcasted int8 from int256, reverting on
     * overflow (when the input is less than smallest int8 or
     * greater than largest int8).
     *
     * Counterpart to Solidity's `int8` operator.
     *
     * Requirements:
     *
     * - input must fit into 8 bits
     *
     * _Available since v3.1._
     */
    function toInt8(int256 value) internal pure returns (int8 downcasted) {
        downcasted = int8(value);
        require(downcasted == value, "SafeCast: value doesn't fit in 8 bits");
    }

    /**
     * @dev Converts an unsigned uint256 into a signed int256.
     *
     * Requirements:
     *
     * - input must be less than or equal to maxInt256.
     *
     * _Available since v3.0._
     */
    function toInt256(uint256 value) internal pure returns (int256) {
        // Note: Unsafe cast below is okay because `type(int256).max` is guaranteed to be positive
        require(value <= uint256(type(int256).max), "SafeCast: value doesn't fit in an int256");
        return int256(value);
    }
}


// File @openzeppelin/contracts/utils/math/Math.sol

// OpenZeppelin Contracts (last updated v4.8.0) (utils/math/Math.sol)

pragma solidity ^0.8.0;

/**
 * @dev Standard math utilities missing in the Solidity language.
 */
library Math {
    enum Rounding {
        Down, // Toward negative infinity
        Up, // Toward infinity
        Zero // Toward zero
    }

    /**
     * @dev Returns the largest of two numbers.
     */
    function max(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }

    /**
     * @dev Returns the smallest of two numbers.
     */
    function min(uint256 a, uint256 b) internal pure returns (uint256) {
        return a < b ? a : b;
    }

    /**
     * @dev Returns the average of two numbers. The result is rounded towards
     * zero.
     */
    function average(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b) / 2 can overflow.
        return (a & b) + (a ^ b) / 2;
    }

    /**
     * @dev Returns the ceiling of the division of two numbers.
     *
     * This differs from standard division with `/` in that it rounds up instead
     * of rounding down.
     */
    function ceilDiv(uint256 a, uint256 b) internal pure returns (uint256) {
        // (a + b - 1) / b can overflow on addition, so we distribute.
        return a == 0 ? 0 : (a - 1) / b + 1;
    }

    /**
     * @notice Calculates floor(x * y / denominator) with full precision. Throws if result overflows a uint256 or denominator == 0
     * @dev Original credit to Remco Bloemen under MIT license (https://xn--2-umb.com/21/muldiv)
     * with further edits by Uniswap Labs also under MIT license.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator
    ) internal pure returns (uint256 result) {
        unchecked {
            // 512-bit multiply [prod1 prod0] = x * y. Compute the product mod 2^256 and mod 2^256 - 1, then use
            // use the Chinese Remainder Theorem to reconstruct the 512 bit result. The result is stored in two 256
            // variables such that product = prod1 * 2^256 + prod0.
            uint256 prod0; // Least significant 256 bits of the product
            uint256 prod1; // Most significant 256 bits of the product
            assembly {
                let mm := mulmod(x, y, not(0))
                prod0 := mul(x, y)
                prod1 := sub(sub(mm, prod0), lt(mm, prod0))
            }

            // Handle non-overflow cases, 256 by 256 division.
            if (prod1 == 0) {
                return prod0 / denominator;
            }

            // Make sure the result is less than 2^256. Also prevents denominator == 0.
            require(denominator > prod1);

            ///////////////////////////////////////////////
            // 512 by 256 division.
            ///////////////////////////////////////////////

            // Make division exact by subtracting the remainder from [prod1 prod0].
            uint256 remainder;
            assembly {
                // Compute remainder using mulmod.
                remainder := mulmod(x, y, denominator)

                // Subtract 256 bit number from 512 bit number.
                prod1 := sub(prod1, gt(remainder, prod0))
                prod0 := sub(prod0, remainder)
            }

            // Factor powers of two out of denominator and compute largest power of two divisor of denominator. Always >= 1.
            // See https://cs.stackexchange.com/q/138556/92363.

            // Does not overflow because the denominator cannot be zero at this stage in the function.
            uint256 twos = denominator & (~denominator + 1);
            assembly {
                // Divide denominator by twos.
                denominator := div(denominator, twos)

                // Divide [prod1 prod0] by twos.
                prod0 := div(prod0, twos)

                // Flip twos such that it is 2^256 / twos. If twos is zero, then it becomes one.
                twos := add(div(sub(0, twos), twos), 1)
            }

            // Shift in bits from prod1 into prod0.
            prod0 |= prod1 * twos;

            // Invert denominator mod 2^256. Now that denominator is an odd number, it has an inverse modulo 2^256 such
            // that denominator * inv = 1 mod 2^256. Compute the inverse by starting with a seed that is correct for
            // four bits. That is, denominator * inv = 1 mod 2^4.
            uint256 inverse = (3 * denominator) ^ 2;

            // Use the Newton-Raphson iteration to improve the precision. Thanks to Hensel's lifting lemma, this also works
            // in modular arithmetic, doubling the correct bits in each step.
            inverse *= 2 - denominator * inverse; // inverse mod 2^8
            inverse *= 2 - denominator * inverse; // inverse mod 2^16
            inverse *= 2 - denominator * inverse; // inverse mod 2^32
            inverse *= 2 - denominator * inverse; // inverse mod 2^64
            inverse *= 2 - denominator * inverse; // inverse mod 2^128
            inverse *= 2 - denominator * inverse; // inverse mod 2^256

            // Because the division is now exact we can divide by multiplying with the modular inverse of denominator.
            // This will give us the correct result modulo 2^256. Since the preconditions guarantee that the outcome is
            // less than 2^256, this is the final result. We don't need to compute the high bits of the result and prod1
            // is no longer required.
            result = prod0 * inverse;
            return result;
        }
    }

    /**
     * @notice Calculates x * y / denominator with full precision, following the selected rounding direction.
     */
    function mulDiv(
        uint256 x,
        uint256 y,
        uint256 denominator,
        Rounding rounding
    ) internal pure returns (uint256) {
        uint256 result = mulDiv(x, y, denominator);
        if (rounding == Rounding.Up && mulmod(x, y, denominator) > 0) {
            result += 1;
        }
        return result;
    }

    /**
     * @dev Returns the square root of a number. If the number is not a perfect square, the value is rounded down.
     *
     * Inspired by Henry S. Warren, Jr.'s "Hacker's Delight" (Chapter 11).
     */
    function sqrt(uint256 a) internal pure returns (uint256) {
        if (a == 0) {
            return 0;
        }

        // For our first guess, we get the biggest power of 2 which is smaller than the square root of the target.
        //
        // We know that the "msb" (most significant bit) of our target number `a` is a power of 2 such that we have
        // `msb(a) <= a < 2*msb(a)`. This value can be written `msb(a)=2**k` with `k=log2(a)`.
        //
        // This can be rewritten `2**log2(a) <= a < 2**(log2(a) + 1)`
        // → `sqrt(2**k) <= sqrt(a) < sqrt(2**(k+1))`
        // → `2**(k/2) <= sqrt(a) < 2**((k+1)/2) <= 2**(k/2 + 1)`
        //
        // Consequently, `2**(log2(a) / 2)` is a good first approximation of `sqrt(a)` with at least 1 correct bit.
        uint256 result = 1 << (log2(a) >> 1);

        // At this point `result` is an estimation with one bit of precision. We know the true value is a uint128,
        // since it is the square root of a uint256. Newton's method converges quadratically (precision doubles at
        // every iteration). We thus need at most 7 iteration to turn our partial result with one bit of precision
        // into the expected uint128 result.
        unchecked {
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            result = (result + a / result) >> 1;
            return min(result, a / result);
        }
    }

    /**
     * @notice Calculates sqrt(a), following the selected rounding direction.
     */
    function sqrt(uint256 a, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = sqrt(a);
            return result + (rounding == Rounding.Up && result * result < a ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 2, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 128;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 64;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 32;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 16;
            }
            if (value >> 8 > 0) {
                value >>= 8;
                result += 8;
            }
            if (value >> 4 > 0) {
                value >>= 4;
                result += 4;
            }
            if (value >> 2 > 0) {
                value >>= 2;
                result += 2;
            }
            if (value >> 1 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 2, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log2(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log2(value);
            return result + (rounding == Rounding.Up && 1 << result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 10, rounded down, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >= 10**64) {
                value /= 10**64;
                result += 64;
            }
            if (value >= 10**32) {
                value /= 10**32;
                result += 32;
            }
            if (value >= 10**16) {
                value /= 10**16;
                result += 16;
            }
            if (value >= 10**8) {
                value /= 10**8;
                result += 8;
            }
            if (value >= 10**4) {
                value /= 10**4;
                result += 4;
            }
            if (value >= 10**2) {
                value /= 10**2;
                result += 2;
            }
            if (value >= 10**1) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log10(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log10(value);
            return result + (rounding == Rounding.Up && 10**result < value ? 1 : 0);
        }
    }

    /**
     * @dev Return the log in base 256, rounded down, of a positive value.
     * Returns 0 if given 0.
     *
     * Adding one to the result gives the number of pairs of hex symbols needed to represent `value` as a hex string.
     */
    function log256(uint256 value) internal pure returns (uint256) {
        uint256 result = 0;
        unchecked {
            if (value >> 128 > 0) {
                value >>= 128;
                result += 16;
            }
            if (value >> 64 > 0) {
                value >>= 64;
                result += 8;
            }
            if (value >> 32 > 0) {
                value >>= 32;
                result += 4;
            }
            if (value >> 16 > 0) {
                value >>= 16;
                result += 2;
            }
            if (value >> 8 > 0) {
                result += 1;
            }
        }
        return result;
    }

    /**
     * @dev Return the log in base 10, following the selected rounding direction, of a positive value.
     * Returns 0 if given 0.
     */
    function log256(uint256 value, Rounding rounding) internal pure returns (uint256) {
        unchecked {
            uint256 result = log256(value);
            return result + (rounding == Rounding.Up && 1 << (result * 8) < value ? 1 : 0);
        }
    }
}


// File contracts/core/interfaces/IMorodexPair.sol

pragma solidity >=0.8.17;

// interfaces


interface IMorodexPair is IERC20, IERC20Permit {
    /**
     * @notice emitted at each mint
     * @param sender address calling the mint function (usualy the Router contract)
     * @param to address that receives the LP-tokens
     * @param amount0 amount of token0 to be added in liquidity
     * @param amount1 amount of token1 to be added in liquidity
     * @dev the amount of LP-token sent can be caught using the transfer event of the pair
     */
    event Mint(address indexed sender, address indexed to, uint256 amount0, uint256 amount1);

    /**
     * @notice emitted at each burn
     * @param sender address calling the burn function (usualy the Router contract)
     * @param to address that receives the tokens
     * @param amount0 amount of token0 to be withdrawn
     * @param amount1 amount of token1 to be withdrawn
     * @dev the amount of LP-token sent can be caught using the transfer event of the pair
     */
    event Burn(address indexed sender, address indexed to, uint256 amount0, uint256 amount1);

    /**
     * @notice emitted at each swap
     * @param sender address calling the swap function (usualy the Router contract)
     * @param to address that receives the out-tokens
     * @param amount0 amount of token0 to be swapped
     * @param amount1 amount of token1 to be swapped
     * @dev one of the 2 amount is always negative, the other one is always positive. The positive one is the one that
     * the user send to the contract, the negative one is the one that the contract send to the user.
     */
    event Swap(address indexed sender, address indexed to, int256 amount0, int256 amount1);

    /**
     * @notice emitted each time the fictive reserves are changed (mint, burn, swap)
     * @param reserve0 the new reserve of token0
     * @param reserve1 the new reserve of token1
     * @param fictiveReserve0 the new fictive reserve of token0
     * @param fictiveReserve1 the new fictive reserve of token1
     * @param priceAverage0 the new priceAverage of token0
     * @param priceAverage1 the new priceAverage of token1
     */
    event Sync(
        uint256 reserve0,
        uint256 reserve1,
        uint256 fictiveReserve0,
        uint256 fictiveReserve1,
        uint256 priceAverage0,
        uint256 priceAverage1
    );

    /**
     * @notice get the factory address
     * @return address of the factory
     */
    function factory() external view returns (address);

    /**
     * @notice get the token0 address
     * @return address of the token0
     */
    function token0() external view returns (address);

    /**
     * @notice get the token1 address
     * @return address of the token1
     */
    function token1() external view returns (address);

    /**
     * @notice called once by the factory at time of deployment
     * @param _token0 address of token0
     * @param _token1 address of token1
     */
    function initialize(address _token0, address _token1) external;

    /**
     * @notice return current Reserves of both token in the pair,
     *  corresponding to token balance - pending fees
     * @return reserve0_ current reserve of token0 - pending fee0
     * @return reserve1_ current reserve of token1 - pending fee1
     */
    function getReserves() external view returns (uint256 reserve0_, uint256 reserve1_);

    /**
     * @notice return current Fictives Reserves of both token in the pair
     * @return fictiveReserve0_ current fictive reserve of token0
     * @return fictiveReserve1_ current fictive reserve of token1
     */
    function getFictiveReserves() external view returns (uint256 fictiveReserve0_, uint256 fictiveReserve1_);

    /**
     * @notice return current pending fees of both token in the pair
     * @return fees0_ current pending fees of token0
     * @return fees1_ current pending fees of token1
     */
    function getFees() external view returns (uint256 fees0_, uint256 fees1_);

    /**
     * @notice return last updated price average at timestamp of both token in the pair,
     *  read price0Average/price1Average for current price of token0/token1
     * @return priceAverage0_ current price for token0
     * @return priceAverage1_ current price for token1
     * @return blockTimestampLast_ last block timestamp when price was updated
     */
    function getPriceAverage()
        external
        view
        returns (uint256 priceAverage0_, uint256 priceAverage1_, uint256 blockTimestampLast_);

    /**
     * @notice return current price average of both token in the pair for provided currentTimeStamp
     *  read price0Average/price1Average for current price of token0/token1
     * @param _fictiveReserveIn,
     * @param _fictiveReserveOut,
     * @param _priceAverageLastTimestamp,
     * @param _priceAverageIn current price for token0
     * @param _priceAverageOut current price for token1
     * @param _currentTimestamp block timestamp to get price
     * @return priceAverageIn_ current price for token0
     * @return priceAverageOut_ current price for token1
     */
    function getUpdatedPriceAverage(
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut,
        uint256 _priceAverageLastTimestamp,
        uint256 _priceAverageIn,
        uint256 _priceAverageOut,
        uint256 _currentTimestamp
    ) external pure returns (uint256 priceAverageIn_, uint256 priceAverageOut_);

    /**
     * @notice Mint lp tokens proportionally of added tokens in balance. Should be called from a contract
     * that makes safety checks like the MorodexRouter
     * @param _to address who will receive minted tokens
     * @param _amount0 amount of token0 to provide
     * @param _amount1 amount of token1 to provide
     * @return liquidity_ amount of lp tokens minted and sent to the address defined in parameter
     */
    function mint(
        address _to,
        uint256 _amount0,
        uint256 _amount1,
        address _payer
    ) external returns (uint256 liquidity_);

    /**
     * @notice Burn lp tokens in the balance of the contract. Sends to the defined address the amount of token0 and
     * token1 proportionally of the amount burned. Should be called from a contract that makes safety checks like the
     * MorodexRouter
     * @param _to address who will receive tokens
     * @return amount0_ amount of token0 sent to the address defined in parameter
     * @return amount1_ amount of token0 sent to the address defined in parameter
     */
    function burn(address _to) external returns (uint256 amount0_, uint256 amount1_);

    /**
     * @notice Swaps tokens. Sends to the defined address the amount of token0 and token1 defined in parameters.
     * Tokens to trade should be already sent in the contract.
     * Swap function will check if the resulted balance is correct with current reserves and reserves fictive.
     * Should be called from a contract that makes safety checks like the MorodexRouter
     * @param _to address who will receive tokens
     * @param _zeroForOne token0 to token1
     * @param _amountSpecified amount of token wanted
     * @param _data used for flash swap, data.length must be 0 for regular swap
     */
    function swap(
        address _to,
        bool _zeroForOne,
        int256 _amountSpecified,
        bytes calldata _data
    ) external returns (int256 amount0_, int256 amount1_);
}


// File contracts/core/libraries/MorodexLibrary.sol

pragma solidity =0.8.17;

// libraries

// interfaces

library MorodexLibrary {
    /// @notice amount of fees sent to LP, not in percent but in FEES_BASE
    uint256 public constant FEES_LP = 5;

    /// @notice amount of fees sent to the pool, not in percent but in FEES_BASE. if feeTo is null, sent to the LP
    uint256 public constant FEES_POOL = 2;

    /// @notice total amount of fees, not in percent but in FEES_BASE
    uint256 public constant FEES_TOTAL = FEES_LP + FEES_POOL;

    /// @notice base of the FEES
    uint256 public constant FEES_BASE = 10000;

    /// @notice ratio of quantity that is send to the user, after removing the fees, not in percent but in FEES_BASE
    uint256 public constant REVERSE_FEES_TOTAL = FEES_BASE - FEES_TOTAL;

    /// @notice precision for approxEq, not in percent but in APPROX_PRECISION_BASE
    uint256 public constant APPROX_PRECISION = 1;

    /// @notice base of the APPROX_PRECISION
    uint256 public constant APPROX_PRECISION_BASE = 1_000_000;

    /// @notice number of seconds to reset priceAverage
    uint256 private constant MAX_BLOCK_DIFF_SECONDS = 300;

    /**
     * @notice check if 2 numbers are approximatively equal, using APPROX_PRECISION
     * @param _x number to compare
     * @param _y number to compare
     * @return true if numbers are approximatively equal, false otherwise
     */
    function approxEq(uint256 _x, uint256 _y) internal pure returns (bool) {
        if (_x > _y) {
            return _x < (_y + (_y * APPROX_PRECISION) / APPROX_PRECISION_BASE);
        } else {
            return _y < (_x + (_x * APPROX_PRECISION) / APPROX_PRECISION_BASE);
        }
    }

    /**
     * @notice check if 2 ratio are approximatively equal: _xNum _/ xDen ~= _yNum / _yDen
     * @param _xNum numerator of the first ratio to compare
     * @param _xDen denominator of the first ratio to compare
     * @param _yNum numerator of the second ratio to compare
     * @param _yDen denominator of the second ratio to compare
     * @return true if ratio are approximatively equal, false otherwise
     */
    function ratioApproxEq(uint256 _xNum, uint256 _xDen, uint256 _yNum, uint256 _yDen) internal pure returns (bool) {
        return approxEq(_xNum * _yDen, _xDen * _yNum);
    }

    /**
     * @notice update priceAverage given old timestamp, new timestamp and prices
     * @param _fictiveReserveIn ratio component of the new price of the in-token
     * @param _fictiveReserveOut ratio component of the new price of the out-token
     * @param _priceAverageLastTimestamp timestamp of the last priceAvregae update (0, if never updated)
     * @param _priceAverageIn ratio component of the last priceAverage of the in-token
     * @param _priceAverageOut ratio component of the last priceAverage of the out-token
     * @param _currentTimestamp timestamp of the priceAverage to update
     * @return newPriceAverageIn_ ratio component of the updated priceAverage of the in-token
     * @return newPriceAverageOut_ ratio component of the updated priceAverage of the out-token
     */
    function getUpdatedPriceAverage(
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut,
        uint256 _priceAverageLastTimestamp,
        uint256 _priceAverageIn,
        uint256 _priceAverageOut,
        uint256 _currentTimestamp
    ) internal pure returns (uint256 newPriceAverageIn_, uint256 newPriceAverageOut_) {
        require(_currentTimestamp >= _priceAverageLastTimestamp, "MorodexPair: INVALID_TIMESTAMP");

        // very first time
        if (_priceAverageLastTimestamp == 0) {
            newPriceAverageIn_ = _fictiveReserveIn;
            newPriceAverageOut_ = _fictiveReserveOut;
        }
        // another tx has been done in the same block
        else if (_priceAverageLastTimestamp == _currentTimestamp) {
            newPriceAverageIn_ = _priceAverageIn;
            newPriceAverageOut_ = _priceAverageOut;
        }
        // need to compute new linear-average price
        else {
            // compute new price:
            uint256 _timeDiff = Math.min(_currentTimestamp - _priceAverageLastTimestamp, MAX_BLOCK_DIFF_SECONDS);

            newPriceAverageIn_ = _fictiveReserveIn;
            newPriceAverageOut_ =
                (((MAX_BLOCK_DIFF_SECONDS - _timeDiff) * _priceAverageOut * newPriceAverageIn_) /
                    _priceAverageIn +
                    _timeDiff *
                    _fictiveReserveOut) /
                MAX_BLOCK_DIFF_SECONDS;
        }
    }

    /**
     * @notice compute the firstTradeAmountIn so that the price reach the price Average
     * @param _amountIn the amountIn requested, it's the maximum possible value for firstAmountIn_
     * @param _fictiveReserveIn fictive reserve of the in-token
     * @param _fictiveReserveOut fictive reserve of the out-token
     * @param _priceAverageIn ratio component of the priceAverage of the in-token
     * @param _priceAverageOut ratio component of the priceAverage of the out-token
     * @return firstAmountIn_ the first amount of in-token
     *
     * @dev if the trade is going in the direction that the price will never reach the priceAverage, or if _amountIn
     * is not big enough to reach the priceAverage or if the price is already equal to the priceAverage, then
     * firstAmountIn_ will be set to _amountIn
     */
    function computeFirstTradeQtyIn(
        uint256 _amountIn,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut,
        uint256 _priceAverageIn,
        uint256 _priceAverageOut
    ) internal pure returns (uint256 firstAmountIn_) {
        // default value
        firstAmountIn_ = _amountIn;

        // if trade is in the good direction
        if (_fictiveReserveOut * _priceAverageIn > _fictiveReserveIn * _priceAverageOut) {
            // pre-compute all operands
            uint256 _toSub = _fictiveReserveIn * (FEES_BASE + REVERSE_FEES_TOTAL - FEES_POOL);
            uint256 _toDiv = (REVERSE_FEES_TOTAL + FEES_LP) << 1;
            uint256 _inSqrt = (((_fictiveReserveIn * _fictiveReserveOut) << 2) / _priceAverageOut) *
                _priceAverageIn *
                (REVERSE_FEES_TOTAL * (FEES_BASE - FEES_POOL)) +
                (_fictiveReserveIn * _fictiveReserveIn * (FEES_LP * FEES_LP));

            // reverse sqrt check to only compute sqrt if really needed
            if (_inSqrt < (_toSub + _amountIn * _toDiv) ** 2) {
                firstAmountIn_ = (Math.sqrt(_inSqrt) - _toSub) / _toDiv;
            }
        }
    }

    /**
     * @notice compute the firstTradeAmountOut so that the price reach the price Average
     * @param _amountOut the amountOut requested, it's the maximum possible value for firstAmountOut_
     * @param _fictiveReserveIn fictive reserve of the in-token
     * @param _fictiveReserveOut fictive reserve of the out-token
     * @param _priceAverageIn ratio component of the priceAverage of the in-token
     * @param _priceAverageOut ratio component of the priceAverage of the out-token
     * @return firstAmountOut_ the first amount of out-token
     *
     * @dev if the trade is going in the direction that the price will never reach the priceAverage, or if _amountOut
     * is not big enough to reach the priceAverage or if the price is already equal to the priceAverage, then
     * firstAmountOut_ will be set to _amountOut
     */
    function computeFirstTradeQtyOut(
        uint256 _amountOut,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut,
        uint256 _priceAverageIn,
        uint256 _priceAverageOut
    ) internal pure returns (uint256 firstAmountOut_) {
        // default value
        firstAmountOut_ = _amountOut;

        // if trade is in the good direction
        if (_fictiveReserveOut * _priceAverageIn > _fictiveReserveIn * _priceAverageOut) {
            // pre-compute all operands
            uint256 _fictiveReserveOutPredFees = (_fictiveReserveIn * FEES_LP * _priceAverageOut) / _priceAverageIn;
            uint256 _toAdd = ((_fictiveReserveOut * REVERSE_FEES_TOTAL) << 1) + _fictiveReserveOutPredFees;
            uint256 _toDiv = REVERSE_FEES_TOTAL << 1;
            uint256 _inSqrt = (((_fictiveReserveOut * _fictiveReserveOutPredFees) << 2) *
                (REVERSE_FEES_TOTAL * (FEES_BASE - FEES_POOL))) /
                FEES_LP +
                _fictiveReserveOutPredFees *
                _fictiveReserveOutPredFees;

            // reverse sqrt check to only compute sqrt if really needed
            if (_inSqrt > (_toAdd - _amountOut * _toDiv) ** 2) {
                firstAmountOut_ = (_toAdd - Math.sqrt(_inSqrt)) / _toDiv;
            }
        }
    }

    /**
     * @notice compute fictive reserves
     * @param _reserveIn reserve of the in-token
     * @param _reserveOut reserve of the out-token
     * @param _fictiveReserveIn fictive reserve of the in-token
     * @param _fictiveReserveOut fictive reserve of the out-token
     * @return newFictiveReserveIn_ new fictive reserve of the in-token
     * @return newFictiveReserveOut_ new fictive reserve of the out-token
     */
    function computeFictiveReserves(
        uint256 _reserveIn,
        uint256 _reserveOut,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut
    ) internal pure returns (uint256 newFictiveReserveIn_, uint256 newFictiveReserveOut_) {
        if (_reserveOut * _fictiveReserveIn < _reserveIn * _fictiveReserveOut) {
            uint256 _temp = (((_reserveOut * _reserveOut) / _fictiveReserveOut) * _fictiveReserveIn) / _reserveIn;
            newFictiveReserveIn_ =
                (_temp * _fictiveReserveIn) /
                _fictiveReserveOut +
                (_reserveOut * _fictiveReserveIn) /
                _fictiveReserveOut;
            newFictiveReserveOut_ = _reserveOut + _temp;
        } else {
            newFictiveReserveIn_ = (_fictiveReserveIn * _reserveOut) / _fictiveReserveOut + _reserveIn;
            newFictiveReserveOut_ = (_reserveIn * _fictiveReserveOut) / _fictiveReserveIn + _reserveOut;
        }

        // div all values by 4
        newFictiveReserveIn_ >>= 2;
        newFictiveReserveOut_ >>= 2;
    }

    /**
     * @notice apply k const rule using fictive reserve, when the amountIn is specified
     * @param _amountIn qty of token that arrives in the contract
     * @param _reserveIn reserve of the in-token
     * @param _reserveOut reserve of the out-token
     * @param _fictiveReserveIn fictive reserve of the in-token
     * @param _fictiveReserveOut fictive reserve of the out-token
     * @return amountOut_ qty of token that leaves in the contract
     * @return newReserveIn_ new reserve of the in-token after the transaction
     * @return newReserveOut_ new reserve of the out-token after the transaction
     * @return newFictiveReserveIn_ new fictive reserve of the in-token after the transaction
     * @return newFictiveReserveOut_ new fictive reserve of the out-token after the transaction
     */
    function applyKConstRuleOut(
        uint256 _amountIn,
        uint256 _reserveIn,
        uint256 _reserveOut,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut
    )
        internal
        pure
        returns (
            uint256 amountOut_,
            uint256 newReserveIn_,
            uint256 newReserveOut_,
            uint256 newFictiveReserveIn_,
            uint256 newFictiveReserveOut_
        )
    {
        // k const rule
        uint256 _amountInWithFee = _amountIn * REVERSE_FEES_TOTAL;
        uint256 _numerator = _amountInWithFee * _fictiveReserveOut;
        uint256 _denominator = _fictiveReserveIn * FEES_BASE + _amountInWithFee;
        amountOut_ = _numerator / _denominator;

        // update new reserves and add lp-fees to pools
        uint256 _amountInWithFeeLp = (_amountInWithFee + (_amountIn * FEES_LP)) / FEES_BASE;
        newReserveIn_ = _reserveIn + _amountInWithFeeLp;
        newFictiveReserveIn_ = _fictiveReserveIn + _amountInWithFeeLp;
        newReserveOut_ = _reserveOut - amountOut_;
        newFictiveReserveOut_ = _fictiveReserveOut - amountOut_;
    }

    /**
     * @notice apply k const rule using fictive reserve, when the amountOut is specified
     * @param _amountOut qty of token that leaves in the contract
     * @param _reserveIn reserve of the in-token
     * @param _reserveOut reserve of the out-token
     * @param _fictiveReserveIn fictive reserve of the in-token
     * @param _fictiveReserveOut fictive reserve of the out-token
     * @return amountIn_ qty of token that arrives in the contract
     * @return newReserveIn_ new reserve of the in-token after the transaction
     * @return newReserveOut_ new reserve of the out-token after the transaction
     * @return newFictiveReserveIn_ new fictive reserve of the in-token after the transaction
     * @return newFictiveReserveOut_ new fictive reserve of the out-token after the transaction
     */
    function applyKConstRuleIn(
        uint256 _amountOut,
        uint256 _reserveIn,
        uint256 _reserveOut,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut
    )
        internal
        pure
        returns (
            uint256 amountIn_,
            uint256 newReserveIn_,
            uint256 newReserveOut_,
            uint256 newFictiveReserveIn_,
            uint256 newFictiveReserveOut_
        )
    {
        // k const rule
        uint256 _numerator = _fictiveReserveIn * _amountOut * FEES_BASE;
        uint256 _denominator = (_fictiveReserveOut - _amountOut) * REVERSE_FEES_TOTAL;
        amountIn_ = _numerator / _denominator + 1;

        // update new reserves
        uint256 _amountInWithFeeLp = (amountIn_ * (REVERSE_FEES_TOTAL + FEES_LP)) / FEES_BASE;
        newReserveIn_ = _reserveIn + _amountInWithFeeLp;
        newFictiveReserveIn_ = _fictiveReserveIn + _amountInWithFeeLp;
        newReserveOut_ = _reserveOut - _amountOut;
        newFictiveReserveOut_ = _fictiveReserveOut - _amountOut;
    }

    /**
     * @notice return the amount of tokens the user would get by doing a swap
     * @param _amountIn quantity of token the user want to swap (to sell)
     * @param _reserveIn reserves of the selling token (getReserve())
     * @param _reserveOut reserves of the buying token (getReserve())
     * @param _fictiveReserveIn fictive reserve of the selling token (getFictiveReserves())
     * @param _fictiveReserveOut fictive reserve of the buying token (getFictiveReserves())
     * @param _priceAverageIn price average of the selling token
     * @param _priceAverageOut price average of the buying token
     * @return amountOut_ The amount of token the user would receive
     * @return newReserveIn_ reserves of the selling token after the swap
     * @return newReserveOut_ reserves of the buying token after the swap
     * @return newFictiveReserveIn_ fictive reserve of the selling token after the swap
     * @return newFictiveReserveOut_ fictive reserve of the buying token after the swap
     */
    function getAmountOut(
        uint256 _amountIn,
        uint256 _reserveIn,
        uint256 _reserveOut,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut,
        uint256 _priceAverageIn,
        uint256 _priceAverageOut
    )
        internal
        pure
        returns (
            uint256 amountOut_,
            uint256 newReserveIn_,
            uint256 newReserveOut_,
            uint256 newFictiveReserveIn_,
            uint256 newFictiveReserveOut_
        )
    {
        require(_amountIn > 0, "MoroDexLibrary: INSUFFICIENT_INPUT_AMOUNT");
        require(
            _reserveIn > 0 && _reserveOut > 0 && _fictiveReserveIn > 0 && _fictiveReserveOut > 0,
            "MoroDexLibrary: INSUFFICIENT_LIQUIDITY"
        );

        uint256 _amountInWithFees = (_amountIn * REVERSE_FEES_TOTAL) / FEES_BASE;
        uint256 _firstAmountIn = computeFirstTradeQtyIn(
            _amountInWithFees,
            _fictiveReserveIn,
            _fictiveReserveOut,
            _priceAverageIn,
            _priceAverageOut
        );

        // if there is 2 trade: 1st trade mustn't re-compute fictive reserves, 2nd should
        if (
            _firstAmountIn == _amountInWithFees &&
            ratioApproxEq(_fictiveReserveIn, _fictiveReserveOut, _priceAverageIn, _priceAverageOut)
        ) {
            (_fictiveReserveIn, _fictiveReserveOut) = computeFictiveReserves(
                _reserveIn,
                _reserveOut,
                _fictiveReserveIn,
                _fictiveReserveOut
            );
        }

        // avoid stack too deep
        {
            uint256 _firstAmountInNoFees = (_firstAmountIn * FEES_BASE) / REVERSE_FEES_TOTAL;
            (
                amountOut_,
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            ) = applyKConstRuleOut(
                _firstAmountInNoFees,
                _reserveIn,
                _reserveOut,
                _fictiveReserveIn,
                _fictiveReserveOut
            );

            // update amountIn in case there is a second trade
            _amountIn -= _firstAmountInNoFees;
        }

        // if we need a second trade
        if (_firstAmountIn < _amountInWithFees) {
            // in the second trade ALWAYS recompute fictive reserves
            (newFictiveReserveIn_, newFictiveReserveOut_) = computeFictiveReserves(
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            );

            uint256 _secondAmountOutNoFees;
            (
                _secondAmountOutNoFees,
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            ) = applyKConstRuleOut(
                _amountIn,
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            );
            amountOut_ += _secondAmountOutNoFees;
        }
    }

    /**
     * @notice return the amount of tokens the user should spend by doing a swap
     * @param _amountOut quantity of token the user want to swap (to buy)
     * @param _reserveIn reserves of the selling token (getReserve())
     * @param _reserveOut reserves of the buying token (getReserve())
     * @param _fictiveReserveIn fictive reserve of the selling token (getFictiveReserves())
     * @param _fictiveReserveOut fictive reserve of the buying token (getFictiveReserves())
     * @param _priceAverageIn price average of the selling token
     * @param _priceAverageOut price average of the buying token
     * @return amountIn_ The amount of token the user would spend to receive _amountOut
     * @return newReserveIn_ reserves of the selling token after the swap
     * @return newReserveOut_ reserves of the buying token after the swap
     * @return newFictiveReserveIn_ fictive reserve of the selling token after the swap
     * @return newFictiveReserveOut_ fictive reserve of the buying token after the swap
     */
    function getAmountIn(
        uint256 _amountOut,
        uint256 _reserveIn,
        uint256 _reserveOut,
        uint256 _fictiveReserveIn,
        uint256 _fictiveReserveOut,
        uint256 _priceAverageIn,
        uint256 _priceAverageOut
    )
        internal
        pure
        returns (
            uint256 amountIn_,
            uint256 newReserveIn_,
            uint256 newReserveOut_,
            uint256 newFictiveReserveIn_,
            uint256 newFictiveReserveOut_
        )
    {
        require(_amountOut > 0, "MoroDexLibrary: INSUFFICIENT_OUTPUT_AMOUNT");
        require(
            _amountOut < _fictiveReserveOut &&
                _reserveIn > 0 &&
                _reserveOut > 0 &&
                _fictiveReserveIn > 0 &&
                _fictiveReserveOut > 0,
            "MoroDexLibrary: INSUFFICIENT_LIQUIDITY"
        );

        uint256 _firstAmountOut = computeFirstTradeQtyOut(
            _amountOut,
            _fictiveReserveIn,
            _fictiveReserveOut,
            _priceAverageIn,
            _priceAverageOut
        );

        // if there is 2 trade: 1st trade mustn't re-compute fictive reserves, 2nd should
        if (
            _firstAmountOut == _amountOut &&
            ratioApproxEq(_fictiveReserveIn, _fictiveReserveOut, _priceAverageIn, _priceAverageOut)
        ) {
            (_fictiveReserveIn, _fictiveReserveOut) = computeFictiveReserves(
                _reserveIn,
                _reserveOut,
                _fictiveReserveIn,
                _fictiveReserveOut
            );
        }

        (amountIn_, newReserveIn_, newReserveOut_, newFictiveReserveIn_, newFictiveReserveOut_) = applyKConstRuleIn(
            _firstAmountOut,
            _reserveIn,
            _reserveOut,
            _fictiveReserveIn,
            _fictiveReserveOut
        );

        // if we need a second trade
        if (_firstAmountOut < _amountOut) {
            // in the second trade ALWAYS recompute fictive reserves
            (newFictiveReserveIn_, newFictiveReserveOut_) = computeFictiveReserves(
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            );

            uint256 _secondAmountIn;
            (
                _secondAmountIn,
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            ) = applyKConstRuleIn(
                _amountOut - _firstAmountOut,
                newReserveIn_,
                newReserveOut_,
                newFictiveReserveIn_,
                newFictiveReserveOut_
            );
            amountIn_ += _secondAmountIn;
        }
    }
}


// File contracts/periphery/libraries/BytesLib.sol

pragma solidity ^0.8.17;

/**
 * @title Solidity Bytes Arrays Utils
 * @author Gonçalo Sá <goncalo.sa@consensys.net>
 * @custom:url https://github.com/GNSPS/solidity-bytes-utils/blob/master/contracts/BytesLib.sol
 *
 * @dev Bytes tightly packed arrays utility library for ethereum contracts written in Solidity.
 *      The library lets you concatenate, slice and type cast bytes arrays both in memory and storage.
 */
library BytesLib {
    function slice(bytes memory _bytes, uint256 _start, uint256 _length) internal pure returns (bytes memory) {
        require(_length + 31 >= _length, "slice_overflow");
        require(_start + _length >= _start, "slice_overflow");
        require(_bytes.length >= _start + _length, "slice_outOfBounds");

        bytes memory tempBytes;

        assembly {
            switch iszero(_length)
            case 0 {
                // Get a location of some free memory and store it in tempBytes as
                // Solidity does for memory variables.
                tempBytes := mload(0x40)

                // The first word of the slice result is potentially a partial
                // word read from the original array. To read it, we calculate
                // the length of that partial word and start copying that many
                // bytes into the array. The first word we copy will start with
                // data we don't care about, but the last `lengthmod` bytes will
                // land at the beginning of the contents of the new array. When
                // we're done copying, we overwrite the full first word with
                // the actual length of the slice.
                let lengthmod := and(_length, 31)

                // The multiplication in the next line is necessary
                // because when slicing multiples of 32 bytes (lengthmod == 0)
                // the following copy loop was copying the origin's length
                // and then ending prematurely not copying everything it should.
                let mc := add(add(tempBytes, lengthmod), mul(0x20, iszero(lengthmod)))
                let end := add(mc, _length)

                for {
                    // The multiplication in the next line has the same exact purpose
                    // as the one above.
                    let cc := add(add(add(_bytes, lengthmod), mul(0x20, iszero(lengthmod))), _start)
                } lt(mc, end) {
                    mc := add(mc, 0x20)
                    cc := add(cc, 0x20)
                } {
                    mstore(mc, mload(cc))
                }

                mstore(tempBytes, _length)

                //update free-memory pointer
                //allocating the array padded to 32 bytes like the compiler does now
                mstore(0x40, and(add(mc, 31), not(31)))
            }
            //if we want a zero-length slice let's just return a zero-length array
            default {
                tempBytes := mload(0x40)
                //zero out the 32 bytes slice we are about to return
                //we need to do it because Solidity does not garbage collect
                mstore(tempBytes, 0)

                mstore(0x40, add(tempBytes, 0x20))
            }
        }

        return tempBytes;
    }

    function toAddress(bytes memory _bytes, uint256 _start) internal pure returns (address) {
        require(_start + 20 >= _start, "toAddress_overflow");
        require(_bytes.length >= _start + 20, "toAddress_outOfBounds");
        address tempAddress;

        assembly {
            tempAddress := div(mload(add(add(_bytes, 0x20), _start)), 0x1000000000000000000000000)
        }

        return tempAddress;
    }

    function toUint24(bytes memory _bytes, uint256 _start) internal pure returns (uint24) {
        require(_start + 3 >= _start, "toUint24_overflow");
        require(_bytes.length >= _start + 3, "toUint24_outOfBounds");
        uint24 tempUint;

        assembly {
            tempUint := mload(add(add(_bytes, 0x3), _start))
        }

        return tempUint;
    }
}


// File contracts/periphery/libraries/Path.sol

pragma solidity ^0.8.17;

// libraries

/**
 * @title Functions for manipulating path data for multihop swaps
 * @custom:from UniswapV3
 * @custom:url https://github.com/Uniswap/v3-periphery/blob/main/contracts/libraries/Path.sol
 */
library Path {
    using BytesLib for bytes;

    /// @dev The length of the bytes encoded address
    uint256 private constant ADDR_SIZE = 20;

    /// @dev The offset of a single token address
    uint256 private constant NEXT_OFFSET = ADDR_SIZE;
    /// @dev The offset of an encoded pool key
    uint256 private constant POP_OFFSET = NEXT_OFFSET + ADDR_SIZE;
    /// @dev The minimum length of an encoding that contains 2 or more pools
    uint256 private constant MULTIPLE_POOLS_MIN_LENGTH = POP_OFFSET + NEXT_OFFSET;

    /// @notice Returns true if the path contains two or more pools
    /// @param path The encoded swap path
    /// @return True if path contains two or more pools, otherwise false
    function hasMultiplePools(bytes memory path) internal pure returns (bool) {
        return path.length >= MULTIPLE_POOLS_MIN_LENGTH;
    }

    /// @notice Returns the number of pools in the path
    /// @param path The encoded swap path
    /// @return The number of pools in the path
    function numPools(bytes memory path) internal pure returns (uint256) {
        // Ignore the first token address. From then on every fee and token offset indicates a pool.
        return ((path.length - ADDR_SIZE) / NEXT_OFFSET);
    }

    /// @notice Decodes the first pool in path
    /// @param path The bytes encoded swap path
    /// @return tokenA The first token of the given pool
    /// @return tokenB The second token of the given pool
    function decodeFirstPool(bytes memory path) internal pure returns (address tokenA, address tokenB) {
        tokenA = path.toAddress(0);
        tokenB = path.toAddress(NEXT_OFFSET);
    }

    /// @notice Gets the segment corresponding to the first pool in the path
    /// @param path The bytes encoded swap path
    /// @return The segment containing all data necessary to target the first pool in the path
    function getFirstPool(bytes memory path) internal pure returns (bytes memory) {
        return path.slice(0, POP_OFFSET);
    }

    /// @notice Skips a token from the buffer and returns the remainder
    /// @param path The swap path
    /// @return The remaining token elements in the path
    function skipToken(bytes memory path) internal pure returns (bytes memory) {
        return path.slice(NEXT_OFFSET, path.length - NEXT_OFFSET);
    }

    function encodeTightlyPacked(address[] memory path) internal pure returns (bytes memory encoded) {
        uint256 len = path.length;
        for (uint256 i = 0; i < len; i++) {
            encoded = bytes.concat(encoded, abi.encodePacked(path[i]));
        }
    }

    function encodeTightlyPackedReversed(address[] memory path) internal pure returns (bytes memory encoded) {
        uint256 len = path.length;
        for (uint256 i = len; i > 0; i--) {
            encoded = bytes.concat(encoded, abi.encodePacked(path[i - 1]));
        }
    }
}


// File @openzeppelin/contracts/interfaces/IERC20.sol

// OpenZeppelin Contracts v4.4.1 (interfaces/IERC20.sol)

pragma solidity ^0.8.0;


// File contracts/core/interfaces/IMorodexFactory.sol

pragma solidity >=0.8.17;

interface IMorodexFactory {
    /**
     * @notice emitted at each MorodexPair created
     * @param token0 address of the token0
     * @param token1 address of the token1
     * @param pair address of the MorodexPair created
     * @param totalPair number of MorodexPair created so far
     */
    event PairCreated(address indexed token0, address indexed token1, address pair, uint256 totalPair);

    /**
     * @notice return which address fees will be transferred
     */
    function feeTo() external view returns (address);

    /**
     * @notice return which address can update feeTo
     */
    function feeToSetter() external view returns (address);

    /**
     * @notice return the address of the pair of 2 tokens
     */
    function getPair(address _tokenA, address _tokenB) external view returns (address pair_);

    /**
     * @notice return the address of the pair at index
     * @param _index index of the pair
     * @return pair_ address of the pair
     */
    function allPairs(uint256 _index) external view returns (address pair_);

    /**
     * @notice return the quantity of pairs
     * @return quantity in uint256
     */
    function allPairsLength() external view returns (uint256);

    /**
     * @notice create pair with 2 address
     * @param _tokenA address of tokenA
     * @param _tokenB address of tokenB
     * @return pair_ address of the pair created
     */
    function createPair(address _tokenA, address _tokenB) external returns (address pair_);

    /**
     * @notice set the address who will receive fees, can only be call by feeToSetter
     * @param _feeTo address to replace
     */
    function setFeeTo(address _feeTo) external;

    /**
     * @notice set the address who can update feeTo, can only be call by feeToSetter
     * @param _feeToSetter address to replace
     */
    function setFeeToSetter(address _feeToSetter) external;
}


// File contracts/core/interfaces/IMorodexSwapCallback.sol

pragma solidity >=0.8.17;

interface IMorodexSwapCallback {
    /**
     * @notice callback data for swap
     * @param _amount0Delta amount of token0 for the swap (negative is incoming, positive is required to pay to pair)
     * @param _amount1Delta amount of token1 for the swap (negative is incoming, positive is required to pay to pair)
     * @param _data for Router path and payer for the swap (see router for details)
     */
    function morodexSwapCallback(int256 _amount0Delta, int256 _amount1Delta, bytes calldata _data) external;
}


// File contracts/rewards/interfaces/IAutoSwapper.sol

pragma solidity 0.8.17;

// interfaces



interface IAutoSwapper is IMorodexSwapCallback {
    /**
     * @notice public function for executing swaps on tokens and send them to staking contract will be called from a
     * Morodex Pair on mint and burn, and can be forced call by anyone
     * @param _token0 token to be converted to mdex
     * @param _token1 token to be converted to mdex
     */
    function executeWork(IERC20 _token0, IERC20 _token1) external;

    /**
     * @notice transfer MDEX from here to staking contract
     */
    function transferTokens() external;

    /**
     * @notice return the factory address
     * @return factory address
     */
    function factory() external view returns (IMorodexFactory);

    /**
     * @notice return the staking address
     * @return staking address
     */
    function stakingAddress() external view returns (address);

    /**
     * @notice return the morodexToken address
     * @return morodexToken address
     */
    function morodexToken() external view returns (IERC20);
}


// File contracts/rewards/AutoSwapper.sol

pragma solidity 0.8.17;

// libraries




// interfaces


/**
 * @title AutoSwapper
 * @notice AutoSwapper makes it automatic and/or public to get fees from Morodex and convert it to tokens for staking
 */
contract AutoSwapper is IAutoSwapper {
    using SafeERC20 for IERC20;
    using SafeCast for uint256;
    using SafeCast for int256;
    using Path for bytes;

    /**
     * @notice callback data for swap from MorodexRouter
     * @param path path of the swap, array of token addresses tightly packed
     * @param payer address of the payer for the swap
     */
    struct SwapCallbackData {
        bytes path;
        address payer;
    }

    /**
     * @notice swap parameters used by function _swapAndSend
     * @param zeroForOne true if we swap the token0 with token1, false otherwise
     * @param balanceIn balance of in-token to be swapped
     * @param pair pair address
     * @param fictiveReserve0 fictive reserve of token0 of the pair
     * @param fictiveReserve1 fictive reserve of token1 of the pair
     * @param oldPriceAv0 priceAverage of token0 of the pair before the swap
     * @param oldPriceAv1 priceAverage of token1 of the pair before the swap
     * @param oldPriceAvTimestamp priceAverageLastTimestamp of the pair before the swap
     * @param newPriceAvIn priceAverage of token0 of the pair after the swap
     * @param newPriceAvOut priceAverage of token1 of the pair after the swap
     */
    struct SwapCallParams {
        bool zeroForOne;
        uint256 balanceIn;
        IMorodexPair pair;
        uint256 fictiveReserve0;
        uint256 fictiveReserve1;
        uint256 oldPriceAv0;
        uint256 oldPriceAv1;
        uint256 oldPriceAvTimestamp;
        uint256 newPriceAvIn;
        uint256 newPriceAvOut;
    }

    bytes4 private constant SWAP_SELECTOR = bytes4(keccak256(bytes("swap(address,bool,int256,bytes)")));
    uint256 private constant AUTOSWAP_SLIPPAGE = 2; // 2%
    uint256 private constant AUTOSWAP_SLIPPAGE_BASE = 100;

    IMorodexFactory public immutable factory;
    address public immutable stakingAddress;
    IERC20 public immutable morodexToken;

    IMorodexPair private constant DEFAULT_CACHED_PAIR = IMorodexPair(address(0));
    IMorodexPair private cachedPair = DEFAULT_CACHED_PAIR;

    constructor(IMorodexFactory _factory, IERC20 _morodexToken, address _stakingAddress) {
        factory = _factory;
        morodexToken = _morodexToken;
        stakingAddress = _stakingAddress;
    }

    /// @inheritdoc IAutoSwapper
    function executeWork(IERC20 _token0, IERC20 _token1) external {
        _swapAndSend(_token0);
        _swapAndSend(_token1);
        transferTokens();
    }

    /// @inheritdoc IAutoSwapper
    function transferTokens() public {
        uint256 _balance = morodexToken.balanceOf(address(this));
        if (_balance == 0) return;
        morodexToken.safeTransfer(stakingAddress, _balance);
    }

    /**
     * @notice private function to swap token in MDEX and send it to the staking address
     * @param _token address of the token to swap into mdex
     */
    function _swapAndSend(IERC20 _token) private {
        if (_token == morodexToken) return;
        SwapCallParams memory _params = SwapCallParams({
            zeroForOne: _token < morodexToken,
            balanceIn: _token.balanceOf(address(this)),
            pair: IMorodexPair(factory.getPair(address(_token), address(morodexToken))),
            fictiveReserve0: 0,
            fictiveReserve1: 0,
            oldPriceAv0: 0,
            oldPriceAv1: 0,
            oldPriceAvTimestamp: 0,
            newPriceAvIn: 0,
            newPriceAvOut: 0
        });

        // basic check on input data
        if (_params.balanceIn == 0 || address(_params.pair) == address(0)) return;

        // get reserves and pricesAv
        (_params.fictiveReserve0, _params.fictiveReserve1) = _params.pair.getFictiveReserves();
        (_params.oldPriceAv0, _params.oldPriceAv1, _params.oldPriceAvTimestamp) = _params.pair.getPriceAverage();

        if (_params.oldPriceAv0 == 0 || _params.oldPriceAv1 == 0) {
            (_params.oldPriceAv0, _params.oldPriceAv1) = (_params.fictiveReserve0, _params.fictiveReserve1);
        }

        if (_params.zeroForOne) {
            (_params.newPriceAvIn, _params.newPriceAvOut) = MorodexLibrary.getUpdatedPriceAverage(
                _params.fictiveReserve0,
                _params.fictiveReserve1,
                _params.oldPriceAvTimestamp,
                _params.oldPriceAv0,
                _params.oldPriceAv1,
                block.timestamp
            );
        } else {
            (_params.newPriceAvIn, _params.newPriceAvOut) = MorodexLibrary.getUpdatedPriceAverage(
                _params.fictiveReserve1,
                _params.fictiveReserve0,
                _params.oldPriceAvTimestamp,
                _params.oldPriceAv1,
                _params.oldPriceAv0,
                block.timestamp
            );
        }

        // we allow for 2% slippage from previous swaps in block
        uint256 _amountOutWithSlippage = (_params.balanceIn *
            _params.newPriceAvOut *
            (AUTOSWAP_SLIPPAGE_BASE - AUTOSWAP_SLIPPAGE)) / (_params.newPriceAvIn * AUTOSWAP_SLIPPAGE_BASE);
        require(_amountOutWithSlippage > 0, "AutoSwapper: slippage calculation failed");

        cachedPair = _params.pair;

        // we dont check for success as we dont want to revert the whole tx if the swap fails
        address(_params.pair).call(
            abi.encodeWithSelector(
                SWAP_SELECTOR,
                stakingAddress,
                _token < morodexToken,
                _params.balanceIn.toInt256(),
                abi.encode(
                    SwapCallbackData({ path: abi.encodePacked(_token, morodexToken), payer: address(this) }),
                    _amountOutWithSlippage
                )
            )
        );

        cachedPair = DEFAULT_CACHED_PAIR;
    }

    /// @inheritdoc IMorodexSwapCallback
    function morodexSwapCallback(int256 _amount0Delta, int256 _amount1Delta, bytes calldata _dataFromPair) external {
        require(_amount0Delta > 0 || _amount1Delta > 0, "MorodexRouter: Callback Invalid amount");
        (SwapCallbackData memory _data, uint256 _amountOutWithSlippage) = abi.decode(
            _dataFromPair,
            (SwapCallbackData, uint256)
        );
        (address _tokenIn, ) = _data.path.decodeFirstPool();
        require(msg.sender == address(cachedPair), "MoroDexRouter: INVALID_PAIR"); // ensure that msg.sender is a pair
        // ensure that the trade gives at least the minimum amount of output token (negative delta)
        require(
            (_amount0Delta < 0 ? uint256(-_amount0Delta) : (-_amount1Delta).toUint256()) >= _amountOutWithSlippage,
            "MorodexAutoSwapper: Invalid price"
        );
        // send positive delta to pair
        IERC20(_tokenIn).safeTransfer(
            msg.sender,
            _amount0Delta > 0 ? uint256(_amount0Delta) : _amount1Delta.toUint256()
        );
    }
}
