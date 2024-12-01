/**
 *Submitted for verification at testnet.bscscan.com on 2024-11-29
*/

/**
 *Submitted for verification at testnet.bscscan.com on 2024-11-26
*/

// File: @openzeppelin/contracts/token/ERC20/IERC20.sol


// OpenZeppelin Contracts (last updated v5.1.0) (token/ERC20/IERC20.sol)
// SPDX-License-Identifier: MIT
pragma solidity ^0.8.20;

/**
 * @dev Interface of the ERC-20 standard as defined in the ERC.
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
     * @dev Returns the value of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the value of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves a `value` amount of tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 value) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets a `value` amount of tokens as the allowance of `spender` over the
     * caller's tokens.
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
    function approve(address spender, uint256 value) external returns (bool);

    /**
     * @dev Moves a `value` amount of tokens from `from` to `to` using the
     * allowance mechanism. `value` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 value) external returns (bool);
}

// File: @openzeppelin/contracts/utils/Context.sol


// OpenZeppelin Contracts (last updated v5.0.1) (utils/Context.sol)

pragma solidity ^0.8.20;

/**
 * @dev Provides information about the current execution context, including the
 * sender of the transaction and its data. While these are generally available
 * via msg.sender and msg.data, they should not be accessed in such a direct
 * manner, since when dealing with meta-transactions the account sending and
 * paying for execution may not be the actual sender (as far as an application
 * is concerned).
 *
 * This contract is only required for intermediate, library-like contracts.
 */
abstract contract Context {
    function _msgSender() internal view virtual returns (address) {
        return msg.sender;
    }

    function _msgData() internal view virtual returns (bytes calldata) {
        return msg.data;
    }

    function _contextSuffixLength() internal view virtual returns (uint256) {
        return 0;
    }
}

// File: @openzeppelin/contracts/access/Ownable.sol


// OpenZeppelin Contracts (last updated v5.0.0) (access/Ownable.sol)

pragma solidity ^0.8.20;


/**
 * @dev Contract module which provides a basic access control mechanism, where
 * there is an account (an owner) that can be granted exclusive access to
 * specific functions.
 *
 * The initial owner is set to the address provided by the deployer. This can
 * later be changed with {transferOwnership}.
 *
 * This module is used through inheritance. It will make available the modifier
 * `onlyOwner`, which can be applied to your functions to restrict their use to
 * the owner.
 */
abstract contract Ownable is Context {
    address private _owner;

    /**
     * @dev The caller account is not authorized to perform an operation.
     */
    error OwnableUnauthorizedAccount(address account);

    /**
     * @dev The owner is not a valid owner account. (eg. `address(0)`)
     */
    error OwnableInvalidOwner(address owner);

    event OwnershipTransferred(address indexed previousOwner, address indexed newOwner);

    /**
     * @dev Initializes the contract setting the address provided by the deployer as the initial owner.
     */
    constructor(address initialOwner) {
        if (initialOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(initialOwner);
    }

    /**
     * @dev Throws if called by any account other than the owner.
     */
    modifier onlyOwner() {
        _checkOwner();
        _;
    }

    /**
     * @dev Returns the address of the current owner.
     */
    function owner() public view virtual returns (address) {
        return _owner;
    }

    /**
     * @dev Throws if the sender is not the owner.
     */
    function _checkOwner() internal view virtual {
        if (owner() != _msgSender()) {
            revert OwnableUnauthorizedAccount(_msgSender());
        }
    }

    /**
     * @dev Leaves the contract without owner. It will not be possible to call
     * `onlyOwner` functions. Can only be called by the current owner.
     *
     * NOTE: Renouncing ownership will leave the contract without an owner,
     * thereby disabling any functionality that is only available to the owner.
     */
    function renounceOwnership() public virtual onlyOwner {
        _transferOwnership(address(0));
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Can only be called by the current owner.
     */
    function transferOwnership(address newOwner) public virtual onlyOwner {
        if (newOwner == address(0)) {
            revert OwnableInvalidOwner(address(0));
        }
        _transferOwnership(newOwner);
    }

    /**
     * @dev Transfers ownership of the contract to a new account (`newOwner`).
     * Internal function without access restriction.
     */
    function _transferOwnership(address newOwner) internal virtual {
        address oldOwner = _owner;
        _owner = newOwner;
        emit OwnershipTransferred(oldOwner, newOwner);
    }
}

// File: @openzeppelin/contracts/security/ReentrancyGuard.sol


// OpenZeppelin Contracts (last updated v4.9.0) (security/ReentrancyGuard.sol)

pragma solidity ^0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}

// File: contract/new.sol


pragma solidity ^0.8.0;




interface IPancakeRouter02 {
    function swapExactTokensForTokensSupportingFeeOnTransferTokens(
        uint256 amountIn,
        uint256 amountOutMin,
        address[] calldata path,
        address to,
        uint256 deadline
    ) external;

    function getAmountsOut(uint256 amountIn, address[] calldata path) 
        external view returns (uint256[] memory amounts);
}

contract PancakeSwapFeeHandler is Ownable, ReentrancyGuard {
    IERC20 public sourceToken; // BUSD or original token
    IERC20 public targetToken; // Token to swap into
    IPancakeRouter02 public pancakeRouter;
    
    uint256 public constant DEADLINE_EXTENSION = 300; // 5 minutes
    uint256 public slippageTolerance = 50; // 0.5% default slippage tolerance (in basis points)

    mapping(address => uint256) public userSwappedTokens;
    mapping(address => bool) public authorizedContracts;

    event TokensReceived(address user, uint256 amount);
    event TokensSwapped(address user, uint256 amountIn, uint256 amountOut);
    event TokensWithdrawn(address user, uint256 amount);
    event SlippageToleranceUpdated(uint256 newTolerance);

    constructor(
        address _sourceToken,
        address _targetToken,
        address _pancakeRouter
    ) Ownable(msg.sender) {
        require(_sourceToken != address(0), "Invalid source token");
        require(_targetToken != address(0), "Invalid target token");
        require(_pancakeRouter != address(0), "Invalid router address");
        
        sourceToken = IERC20(_sourceToken);
        targetToken = IERC20(_targetToken);
        pancakeRouter = IPancakeRouter02(_pancakeRouter);
    }

    modifier onlyAuthorized() {
        require(authorizedContracts[msg.sender], "Not authorized");
        _;
    }

    function setAuthorizedContract(address _contract, bool _authorized) external onlyOwner {
        require(_contract != address(0), "Invalid contract address");
        authorizedContracts[_contract] = _authorized;
    }

    function setSlippageTolerance(uint256 _newTolerance) external onlyOwner {
        require(_newTolerance <= 1000, "Slippage tolerance too high"); // Max 10%
        slippageTolerance = _newTolerance;
        emit SlippageToleranceUpdated(_newTolerance);
    }

    function calculateMinimumOutputAmount(uint256 expectedAmount) internal view returns (uint256) {
        return expectedAmount * (10000 - slippageTolerance) / 10000;
    }

    // Function to receive and swap tokens
    function handleFeeAndSwap(address user, uint256 amount) external onlyAuthorized nonReentrant {
        require(user != address(0), "Invalid user address");
        require(amount > 0, "Amount must be greater than 0");

        // Transfer tokens from the sender
        require(
            sourceToken.transferFrom(msg.sender, address(this), amount),
            "Transfer failed"
        );
        emit TokensReceived(user, amount);

        // Calculate expected output amount
        address[] memory path = new address[](2);
        path[0] = address(sourceToken);
        path[1] = address(targetToken);

        uint256[] memory expectedAmounts = pancakeRouter.getAmountsOut(amount, path);
        uint256 minimumOutput = calculateMinimumOutputAmount(expectedAmounts[1]);

        // Approve router to spend source tokens
        sourceToken.approve(address(pancakeRouter), amount);

        // Get initial balance of target token
        uint256 initialTargetBalance = targetToken.balanceOf(address(this));

        // Execute swap with support for tokens that take fees on transfer
        pancakeRouter.swapExactTokensForTokensSupportingFeeOnTransferTokens(
            amount,
            minimumOutput,
            path,
            address(this),
            block.timestamp + DEADLINE_EXTENSION
        );

        // Calculate actual received amount
        uint256 finalTargetBalance = targetToken.balanceOf(address(this));
        uint256 actualReceivedAmount = finalTargetBalance - initialTargetBalance;

        // Record swapped amount for user
        userSwappedTokens[user] += actualReceivedAmount;
        emit TokensSwapped(user, amount, actualReceivedAmount);
    }

    // Function for users to withdraw their swapped tokens
    function withdrawSwappedTokens() external nonReentrant {
        uint256 amount = userSwappedTokens[msg.sender];
        require(amount > 0, "No tokens to withdraw");

        userSwappedTokens[msg.sender] = 0;
        require(
            targetToken.transfer(msg.sender, amount),
            "Transfer failed"
        );
        emit TokensWithdrawn(msg.sender, amount);
    }

    // View function to check available tokens
    function getAvailableTokens(address user) external view returns (uint256) {
        return userSwappedTokens[user];
    }

    // Emergency withdraw function for owner
    function emergencyWithdraw(address token) external onlyOwner {
        require(token != address(0), "Invalid token address");
        uint256 balance = IERC20(token).balanceOf(address(this));
        require(balance > 0, "No tokens to withdraw");
        require(
            IERC20(token).transfer(msg.sender, balance),

            "Transfer failed"
        );
    }

    // View function to simulate swap output
    function getExpectedOutputAmount(uint256 inputAmount) external view returns (uint256) {
        address[] memory path = new address[](2);
        
        path[0] = address(sourceToken);
        path[1] = address(targetToken);
        
        uint256[] memory amounts = pancakeRouter.getAmountsOut(inputAmount, path);
        return amounts[1];
    }
}
