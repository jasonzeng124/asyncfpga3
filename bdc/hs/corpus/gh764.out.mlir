module {
  handshake.func @test_and_sext_unknown(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "end"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi0"} : <i1> to <i32>
    %1 = andi %0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %1, %arg2 : <i32>, <>
  }
}


// -----
module {
  handshake.func @test_and_sext_zext(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "end"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i1> to <i16>
    %1 = andi %0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i16>
    %2 = extui %1 {handshake.name = "extui1"} : <i16> to <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %2, %arg2 : <i32>, <>
  }
}


// -----
module {
  handshake.func @test_and_sext_sext(%arg0: !handshake.channel<i1>, %arg1: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["var2", "start"], resNames = ["out0", "end"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi1"} : <i1> to <i7>
    %1 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = -57 : i7} : <>, <i7>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %3 = andi %0, %1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i7>
    %4 = extui %3 {handshake.name = "extui0"} : <i7> to <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %4, %arg1 : <i32>, <>
  }
}

