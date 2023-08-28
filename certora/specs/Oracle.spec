methods {
    // DataStore
    function _.getUint(bytes32) external => DISPATCHER(true);
    function _.getAddress(bytes32) external => DISPATCHER(true);
    function _.getBytes32(bytes32) external => DISPATCHER(true);
    // RoleStore
    function _.hasRole(address,bytes32) external => DISPATCHER(true);
    // OracleStore
    function _.getSigner(uint256) external => DISPATCHER(true);
    // PriceFeed
    function _.latestRoundData() external => DISPATCHER(true);
    /// Chain
    function _.arbBlockNumber() external => ghostBlockNumber() expect uint256 ALL;
    function _.arbBlockHash(uint256 blockNumber) external => ghostBlockHash(blockNumber) expect bytes32 ALL;
    /// Oracle summaries
    /// Getters:
    function OracleHarness.primaryPrices(address) external returns (uint256,uint256);
    function OracleHarness.secondaryPrices(address) external returns (uint256,uint256);
    function OracleHarness.customPrices(address) external returns (uint256,uint256);
    function OracleHarness.getSignerByInfo(uint256, uint256) external returns (address);
    function getPriceFeedPriceRaw(address token) external returns(int256) envfree;
}

ghost ghostBlockNumber() returns uint256 {
    axiom ghostBlockNumber() !=0;
}

ghost ghostBlockHash(uint256) returns bytes32 {
    axiom forall uint256 value1. forall uint256 value2. 
        value1 != value2 => ghostBlockHash(value1) != ghostBlockHash(value2);
}

function ghostMedian(uint256[] array) returns uint256 {
    uint256 med;
    uint256 len = array.length;
    require med >= array[0] && med <= array[require_uint256(len-1)];
    return med;
}

rule getPriceFeedPriceOnlyReturnsPriceGT0(
    env e,
    address token
) {
    
    bool hasFeed;
    uint256 price;
    hasFeed, price = getPriceFeedPrice(e, token);
    if (price > 0) { 
        assert hasFeed;
    }

    assert true;
}

rule getPriceFeedPriceShouldRevertWhenPriceFeedPriceInvalid(
    env e,
    address token
) {
    int rawPrice = getPriceFeedPriceRaw(token);
    bool hasFeed;
    uint256 adjustedPrice;
    hasFeed, adjustedPrice = getPriceFeedPrice(e, token);
    bool didRevert = lastReverted;

    if (rawPrice <= 0) { 
        assert didRevert, "should revert";
    }

    assert true;
}