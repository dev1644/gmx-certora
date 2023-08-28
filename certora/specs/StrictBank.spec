methods {
    // ERC20
    function _.name()                                external  => DISPATCHER(true);
    function _.symbol()                              external  => DISPATCHER(true);
    function _.decimals()                            external  => DISPATCHER(true);
    function _.totalSupply()                         external  => DISPATCHER(true);
    function _.balanceOf(address)                    external  => DISPATCHER(true);
    function _.allowance(address,address)            external  => DISPATCHER(true);
    function _.approve(address,uint256)              external  => DISPATCHER(true);
    function _.transfer(address,uint256)             external  => DISPATCHER(true);
    function _.transferFrom(address,address,uint256) external  => DISPATCHER(true);

    // DataStore
    function _.getUint(bytes32) external => DISPATCHER(true);
    function _.getAddress(bytes32) external => DISPATCHER(true);
    function _.getBytes32(bytes32) external => DISPATCHER(true);
    // RoleStore
    function _.hasRole(address,bytes32) external => DISPATCHER(true);

    // WNT
    function _.deposit()                             external  => DISPATCHER(true);
    function _.withdraw(uint256)                     external  => DISPATCHER(true);
    function tokenBalances(address) external returns (uint256) envfree;

    // Harness
    function balanceOf(address, address) external returns (uint256) envfree;
    function fetchHoldingAddress() external returns (address) envfree;
    function fetchTokenGasLimit(address token) external returns (uint256) envfree;
}

rule sanity_satisfy(method f) {
    env e;
    calldataarg args;
    f(e, args);
    satisfy true;
}

rule transferOutwardAccuracy(
    env e,
    address token,
    address to,
    uint256 tokenAmount
) {
    require to != 0;

    mathint previousCurrentBalance = balanceOf(token, currentContract);
    mathint previousToTokenBalance = balanceOf(token, to);
    mathint previousTokenBalanceOfHoldingAddress = balanceOf(token, fetchHoldingAddress());
    require previousTokenBalanceOfHoldingAddress == 0;

    transferOut@withrevert(e, token, to, tokenAmount);
    bool didRevert = lastReverted;

    mathint afterCurrentBalance = balanceOf(token, currentContract);
    mathint afterToTokenBalance = balanceOf(token, to);
    mathint tokenBalancesAfter = tokenBalances(token);
    mathint afterTokenBalanceOfHoldingAddress = balanceOf(token, fetchHoldingAddress());


    bool isController = isController(e);

    if(!didRevert) {
        assert afterCurrentBalance == previousCurrentBalance - tokenAmount, "deducting correct amount from contract";
        assert tokenBalancesAfter == afterCurrentBalance, "Should update tokenBalances";

        if(tokenAmount + previousToTokenBalance <  2^256) 
            assert previousToTokenBalance + tokenAmount == afterToTokenBalance, "Should updated to address correctly";
    
        if(tokenAmount + previousToTokenBalance >= 2^256)
            assert afterTokenBalanceOfHoldingAddress == previousTokenBalanceOfHoldingAddress + tokenAmount, "Should update receiver address correctly";    
    } else {
      assert ((fetchHoldingAddress() == 0 && tokenAmount + previousToTokenBalance >=  2^256)
        ||to_mathint(tokenAmount) > previousCurrentBalance
        || fetchTokenGasLimit(token) == 0 && tokenAmount != 0
        ||!isController 
        || to == currentContract
        );
    }

    assert true;
}


rule transferInwardAccuracy(
    env e,
    address token
) {
    mathint preTokenbalance = balanceOf(token, currentContract);
    mathint prevPreTokenbalacnce = tokenBalances(token);
    mathint currentBalance = recordTransferIn@withrevert(e, token);
    
    bool didRevert = lastReverted;

    mathint actualTokenBalanceAfter = balanceOf(token, currentContract);
    mathint lastRecordedTokenBalanceAfter = tokenBalances(token);

    assert preTokenbalance == actualTokenBalanceAfter, "recordTransferIn should not ripple other state";
   
    bool isController = isController(e);

    if(!didRevert) {
        assert preTokenbalance - prevPreTokenbalacnce == currentBalance, "correct amount";
        assert lastRecordedTokenBalanceAfter == actualTokenBalanceAfter, "recordTransferIn correcteness";
    } else {
        assert (preTokenbalance - prevPreTokenbalacnce < 0 || !isController), "function should revert if caller does not have controller role";
    }

    assert true;
}


rule verifyBalanceAccuracy(
    env e,
    address token
) {
    uint256 tokenbalance = balanceOf(token, currentContract);

    uint256 currentBalance = syncTokenBalance@withrevert(e, token);
    bool didRevert = lastReverted;

    uint256 postBalance = tokenBalances(token);

    if(!didRevert) {
        assert (currentBalance == tokenbalance && postBalance == tokenbalance);
    }

    bool isController = isController(e);
    assert (didRevert || isController);
}

rule exclusivenessOfBalance(method f, env e, address token, address otherToken) filtered {
        f -> f.selector == sig:recordTransferIn(address).selector 
        || f.selector == sig:afterTransferOut(address).selector
        || f.selector == sig:syncTokenBalance(address).selector
} {
    uint256 preBalance = tokenBalances(otherToken);

    if (f.selector == sig:recordTransferIn(address).selector) {
        recordTransferIn(e, token);
    }
    
    if (f.selector == sig:syncTokenBalance(address).selector) {
        syncTokenBalance(e, token);
    }
    
    if (f.selector == sig:afterTransferOut(address).selector) {
        afterTransferOut(e, token);
    }

    uint256 postBalance = tokenBalances(e, otherToken); 

    assert (otherToken == token || preBalance == postBalance);
}
