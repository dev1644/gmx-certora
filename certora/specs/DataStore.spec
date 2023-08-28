methods {
    function getUint(bytes32 key) external returns (uint256) envfree;
    function getInt(bytes32 key) external returns (int256) envfree;

    // RoleStore.sol
    function _.hasRole(address, bytes32) external => DISPATCHER(true);
}


ghost mapping(bytes32 => mapping(mathint => bytes32)) localUintValues {
    init_state axiom forall bytes32 k. forall mathint x. localUintValues[k][x] == to_bytes32(0);
}
ghost mapping(bytes32 => mapping(bytes32 => uint256)) localUintIndexes {
    init_state axiom forall bytes32 k. forall bytes32 x. localUintIndexes[k][x] == 0;
}
ghost mapping(bytes32 => uint256) localUintLength {
    init_state axiom forall bytes32 k. localUintLength[k] == 0;
    axiom forall bytes32 k. localUintLength[k] < 0xffffffffffffffffffffffffffffffff;
}

hook Sstore currentContract.uintSets[KEY bytes32 setKey].(offset 0) uint256 newLength STORAGE {
    localUintLength[setKey] = newLength;
}

hook Sstore currentContract.uintSets[KEY bytes32 setKey]._inner._values[INDEX uint256 index] bytes32 newValue STORAGE {
    localUintValues[setKey][index] = newValue;
}
hook Sstore currentContract.uintSets[KEY bytes32 setKey]._inner._indexes[KEY bytes32 value] uint256 newIndex STORAGE {
    localUintIndexes[setKey][value] = newIndex;
}

hook Sload uint256 length currentContract.uintSets[KEY bytes32 setKey].(offset 0) STORAGE {
    require localUintLength[setKey] == length;
}
hook Sload bytes32 value currentContract.uintSets[KEY bytes32 setKey]._inner._values[INDEX uint256 index] STORAGE {
    require localUintValues[setKey][index] == value;
}
hook Sload uint256 index currentContract.uintSets[KEY bytes32 setKey]._inner._indexes[KEY bytes32 value] STORAGE {
    require localUintIndexes[setKey][value] == index;
}


rule verifySetUint(
    env e,
    bytes32 key,
    bytes32 differentKey,
    uint256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    uint256 preRandomValue = getUint(differentKey);

    uint256 currentValue = setUint@withrevert(e, key, value);
    bool didRevert = lastReverted;

    uint256 postValue = getUint(key);
    uint256 postRandomValue = getUint(differentKey);

    if(didRevert) {
        assert !isController, "expecting Revert";
    }  else {
        assert value == currentValue && value == postValue, "correct setter and getter functionality";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

rule verifyRemoveUint(
    env e,
    bytes32 key,
    bytes32 differentKey
) {
    require (differentKey != key);

    bool isController = isController(e);
    uint256 preRandomValue = getUint(differentKey);

    removeUint@withrevert(e, key);
    bool didRevert = lastReverted;

    uint256 postValue = getUint(key);
    uint256 postRandomValue = getUint(differentKey);

    if(didRevert) {
        assert !isController, "expecting Revert";
    } else {
        assert postValue == 0, "verifying different ";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

rule verifyApplyDeltaToUint(
    env e,
    bytes32 key,
    bytes32 differentKey,
    int256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getUint(key);
    mathint preRandomValue = getUint(differentKey);

    uint256 currentValue = applyDeltaToUint@withrevert(e, key, value, "");
    bool didRevert = lastReverted;

    mathint postValue = getUint(key);
    mathint postRandomValue = getUint(differentKey);

    if(!didRevert) {
        assert isController;
        assert (0 <= valueBefore + to_mathint(value)) && (valueBefore + to_mathint(value) < 2^256) && (to_mathint(value) != -2^255), "revert if caller does not have controller role";
        assert (postValue == valueBefore + to_mathint(value) && to_mathint(currentValue) == postValue), "correct setter and getter functionality";
    }

    assert true;
}

rule verifyApplyDeltaToUintAccuracy(
    env e,
    bytes32 key,
    bytes32 differentKey,
    uint256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getUint(key);
    mathint preRandomValue = getUint(differentKey);

    uint256 currentValue = applyDeltaToUint@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getUint(key);
    mathint postRandomValue = getUint(differentKey);

    if(didRevert) {
        assert !isController || valueBefore + to_mathint(value) >= 2^256, "expecting revert";
    } else {
        assert (postValue == valueBefore + to_mathint(value) && currentValue == assert_uint256(postValue)), "value verification";
    }

    assert true;
}


rule verifyApplyBoundedDeltaToUintAccuracy(
    env e,
    bytes32 key,
    bytes32 differentKey,
    int256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getUint(key);
    mathint preRandomValue = getUint(differentKey);

    uint256 currentValue = applyBoundedDeltaToUint@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getUint(key);
    mathint postRandomValue = getUint(differentKey);

    if(!isController) {
        assert didRevert, "expecting revert";
    } 
    
    if (!didRevert){
        if(value < 0 && valueBefore + to_mathint(value) < 0) {
            assert postValue == 0 && assert_uint256(currentValue) == 0, "verifying correct Set";
        }

        if(valueBefore + to_mathint(value) >= 0) {
            assert  (postValue == valueBefore + to_mathint(value) && currentValue == assert_uint256(postValue)), "applyBoundedDeltaToUint should set the value";
        }
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

rule verifyIncrementUint(
    env e,
    bytes32 key,
    bytes32 differentKey,
    uint256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getUint(key);
    mathint preRandomValue = getUint(differentKey);

    uint256 currentValue = incrementUint@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getUint(key);
    mathint postRandomValue = getUint(differentKey);

    if (didRevert) {
        assert !isController || valueBefore + to_mathint(value) >= 2^256;
    } else {
        assert (postValue == valueBefore + to_mathint(value) && to_mathint(currentValue) == postValue);
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";

}

rule verifyDecrementUint(
    env e,
    bytes32 key,
    bytes32 differentKey,
    uint256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getUint(key);
    mathint preRandomValue = getUint(differentKey);

    uint256 currentValue = decrementUint@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getUint(key);
    mathint postRandomValue = getUint(differentKey);

    if (didRevert) {
        assert (!isController || valueBefore - to_mathint(value) < 0);
    } else {
        assert (postValue == valueBefore - to_mathint(value) && to_mathint(currentValue) == postValue), "correct setter and getter functionality";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

rule verifySetInt(
    env e,
    bytes32 key,
    bytes32 differentKey,
    int256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    int256 preRandomValue = getInt(differentKey);

    int256 currentValue = setInt@withrevert(e, key, value);
    bool didRevert = lastReverted;

    int256 postValue = getInt(key);
    int256 postRandomValue = getInt(differentKey);

    if(didRevert) {
        assert !isController;
    } else {
        assert (value == currentValue && value == postValue), "correct setter and getter functionality";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

rule verifyRemoveInt(
    env e,
    bytes32 key,
    bytes32 differentKey
) {
    require (differentKey != key);

    bool isController = isController(e);
    int256 preRandomValue = getInt(differentKey);

    removeInt@withrevert(e, key);
    bool removeIntReverted = lastReverted;

    int256 postValue = getInt(key);
    int256 postRandomValue = getInt(differentKey);

    if(removeIntReverted) {
        assert !isController, "expecting revert";
    } else {
        assert postValue == 0, "removal verification";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

//FIXME gas optimization possible, see below
rule verifyApplyDeltaToInt(
    env e,
    bytes32 key,
    bytes32 differentKey,
    int256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getInt(key);
    mathint preRandomValue = getInt(differentKey);

    int256 currentValue = applyDeltaToInt@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getInt(key);
    mathint postRandomValue = getInt(differentKey);

    if(!didRevert) {
        assert isController;
        assert (-2^255 <= valueBefore + to_mathint(value) && valueBefore + to_mathint(value) < 2^255), "revert if caller does not have controller role";
        assert (postValue == valueBefore + to_mathint(value) && to_mathint(currentValue) == postValue), "correct setter and getter functionality";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}


rule verifyIncrementInt(
    env e,
    bytes32 key,
    bytes32 differentKey,
    int256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getInt(key);
    mathint preRandomValue = getInt(differentKey);

    int256 currentValue = incrementInt@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getInt(key);
    mathint postRandomValue = getInt(differentKey);

    if(!didRevert) {
        assert isController;
        assert (-2^255 <= valueBefore + to_mathint(value) && valueBefore + to_mathint(value) < 2^255), "revert if caller does not have controller role";
        assert postValue == valueBefore + to_mathint(value) && to_mathint(currentValue) == postValue, "correct setter and getter functionality";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}

rule verifyDecrementInt(
    env e,
    bytes32 key,
    bytes32 differentKey,
    int256 value
) {
    require (differentKey != key);

    bool isController = isController(e);
    mathint valueBefore = getInt(key);
    mathint preRandomValue = getInt(differentKey);

    int256 currentValue = decrementInt@withrevert(e, key, value);
    bool didRevert = lastReverted;

    mathint postValue = getInt(key);
    mathint postRandomValue = getInt(differentKey);

    if(!didRevert) {
        assert isController; 
        assert (-2^255 <= valueBefore - to_mathint(value) && valueBefore - to_mathint(value) < 2^255), "only revert if caller does not hold controller role or an overflow occures";
        assert postValue == valueBefore - to_mathint(value) && to_mathint(currentValue) == postValue, "correct setter and getter functionality";
    }

    assert preRandomValue == postRandomValue, "should not mutate differentKey state";
}


invariant uintSetsInvariant()
    forall bytes32 setKey .(
        (forall uint256 index. 0 <= index && index < localUintLength[setKey] => to_mathint(localUintIndexes[setKey][localUintValues[setKey][index]]) == index + 1)
     && (forall bytes32 value. localUintIndexes[setKey][value] == 0 ||
         (localUintValues[setKey][localUintIndexes[setKey][value] - 1] == value && localUintIndexes[setKey][value] >= 1 && localUintIndexes[setKey][value] <= localUintLength[setKey])))
    filtered {
        f -> f.selector != sig:setBoolArray(bytes32, bool[]).selector
}