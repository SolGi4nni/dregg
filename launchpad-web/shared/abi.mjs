// abi.mjs — the DreggLaunchpad + DreggLaunchToken ABI the product layer drives.
//
// These fragments mirror EXACTLY the deployed engine at
//   chain/contracts/launchpad/DreggLaunchpad.sol
//   chain/contracts/launchpad/DreggLaunchToken.sol
// There is NO mirror of the mechanism here — the frontend/backend only read and
// call the real contract. The seal preimage is computed by calling the on-chain
// `sealOf` view (drift-free: the same keccak(abi.encode(price,qty,salt,bidder))
// the contract checks in revealBid), never re-derived in JS.

// Phase enum (DreggLaunchpad.Phase)
export const PHASE = ['None', 'Commit', 'Reveal', 'Cleared', 'Finalized'];

// The Schedule tuple signature — kept in one place (registerLaunch + checkSchedule
// must match the on-chain struct field order EXACTLY).
const SCHEDULE =
  '(uint256 totalSupply,uint256 saleSupply,uint256 creatorAllocation,uint256 poolAllocation,uint64 creatorLockUntil,uint256 reservePrice,uint16 graduationBps)';

// Human-readable ABI (ethers v6 parses these directly).
export const LAUNCHPAD_ABI = [
  // ── registration ──
  `function registerLaunch(string tokenName, string tokenSymbol, ${SCHEDULE} s, uint64 commitDuration, uint64 revealDuration, address gate, address attestor) returns (uint256 launchId)`,
  `function checkSchedule(uint256 launchId, ${SCHEDULE} s) view returns (bool)`,
  // ── sealed commit → reveal ──
  'function commitBid(uint256 launchId, bytes32 sealedHash, bytes proof) payable',
  'function revealBid(uint256 launchId, uint256 price, uint256 qty, bytes32 salt)',
  'function sealOf(uint256 price, uint256 qty, bytes32 salt, address bidder) pure returns (bytes32)',
  // ── uniform-price clearing ──
  'function finalizeClearing(uint256 launchId, uint256[] order, bytes clearingProof)',
  // ── non-custodial settlement ──
  'function settleBid(uint256 launchId, address bidder)',
  'function withdrawProceeds(uint256 launchId)',
  'function claimCreatorAllocation(uint256 launchId)',
  // ── graduation (into the provably-solvent liquid market) ──
  'function graduate(uint256 launchId, uint256 claimedQuoteSeed, uint256 claimedTokenSeed) returns (address pool)',
  'function graduationSeed(uint256 launchId) view returns (uint256 quoteSeed, uint256 tokenSeed)',
  'function graduationParamsOf(uint256 launchId) view returns (uint256 poolAllocation, uint16 graduationBps)',
  'function isGraduated(uint256 launchId) view returns (bool)',
  'function poolOf(uint256 launchId) view returns (address)',
  'function proceedsOf(uint256 launchId) view returns (uint256)',
  'function FLOOR_BPS() view returns (uint16)',
  // ── views ──
  'function launchCount() view returns (uint256)',
  'function TOKEN_UNIT() view returns (uint256)',
  'function phaseOf(uint256 launchId) view returns (uint8)',
  'function clearingPriceOf(uint256 launchId) view returns (uint256)',
  'function soldQtyOf(uint256 launchId) view returns (uint256)',
  'function tokenOf(uint256 launchId) view returns (address)',
  'function scheduleCommitOf(uint256 launchId) view returns (bytes32)',
  'function clearingAttested(uint256 launchId) view returns (bool)',
  'function revealedCount(uint256 launchId) view returns (uint256)',
  'function getBid(uint256 launchId, address bidder) view returns (bool committed, bool revealed, uint256 price, uint256 qty, uint256 filled, bool settled, uint256 deposit)',
  // ── events ──
  'event LaunchRegistered(uint256 indexed launchId, address indexed creator, address token, bytes32 scheduleCommit, uint64 commitEnd, uint64 revealEnd)',
  'event BidCommitted(uint256 indexed launchId, address indexed bidder, bytes32 sealedHash, uint256 deposit)',
  'event BidRevealed(uint256 indexed launchId, address indexed bidder, uint256 price, uint256 qty)',
  'event Cleared(uint256 indexed launchId, uint256 clearingPrice, uint256 soldQty, bool attested)',
  'event BidSettled(uint256 indexed launchId, address indexed bidder, uint256 filled, uint256 paid, uint256 refunded)',
  'event ProceedsWithdrawn(uint256 indexed launchId, address indexed creator, uint256 amount)',
  'event CreatorAllocationClaimed(uint256 indexed launchId, address indexed creator, uint256 amount)',
  'event Graduated(uint256 indexed launchId, address indexed pool, uint256 quoteSeed, uint256 tokenSeed, uint256 floorQuote, uint256 floorToken)',
];

// The graduated DreggSolventPool — the provably-solvent liquid market. The token
// page reads its reserves/price/floors and the browser trades against it directly.
export const POOL_ABI = [
  'function token() view returns (address)',
  'function launchId() view returns (uint256)',
  'function reserveQuote() view returns (uint256)',
  'function reserveToken() view returns (uint256)',
  'function floorQuote() view returns (uint256)',
  'function floorToken() view returns (uint256)',
  'function feeBps() view returns (uint16)',
  'function initialized() view returns (bool)',
  'function reserves() view returns (uint256 quote, uint256 tokenR)',
  'function floors() view returns (uint256 quote, uint256 tokenR)',
  'function spotPriceWeiPerToken() view returns (uint256)',
  'function quoteBuy(uint256 quoteIn) view returns (uint256 tokenOut)',
  'function buy(uint256 minTokenOut) payable returns (uint256 tokenOut)',
  'function sell(uint256 tokenIn, uint256 minQuoteOut) returns (uint256 quoteOut)',
  'event Bought(address indexed buyer, uint256 quoteIn, uint256 tokenOut, uint256 reserveQuote, uint256 reserveToken)',
  'event Sold(address indexed seller, uint256 tokenIn, uint256 quoteOut, uint256 reserveQuote, uint256 reserveToken)',
];

export const TOKEN_ABI = [
  'function name() view returns (string)',
  'function symbol() view returns (string)',
  'function decimals() view returns (uint8)',
  'function totalSupply() view returns (uint256)',
  'function cap() view returns (uint256)',
  'function minted() view returns (bool)',
  'function balanceOf(address) view returns (uint256)',
  'event Transfer(address indexed from, address indexed to, uint256 value)',
];
