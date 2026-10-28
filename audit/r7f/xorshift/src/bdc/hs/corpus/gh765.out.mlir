module {
  handshake.func @test_and_sext_sext(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "end"]} {
    %0 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi2"} : <i1> to <i16>
    %1 = ori %0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i16>
    %2 = extsi %1 {handshake.name = "extsi3"} : <i16> to <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %2, %arg2 : <i32>, <>
  }
}


// -----
module {
  handshake.func @test_and_sext_zext(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "end"]} {
    %0 = extui %arg1 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i16> to <i17>
    %1 = extsi %arg0 {handshake.bb = 0 : ui32, handshake.name = "extsi2"} : <i1> to <i17>
    %2 = ori %1, %0 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i17>
    %3 = extsi %2 {handshake.name = "extsi3"} : <i17> to <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %3, %arg2 : <i32>, <>
  }
}


// -----
module {
  handshake.func @test_and_zext_sext(%arg0: !handshake.channel<i1>, %arg1: !handshake.channel<i16>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["arg0", "arg1", "start"], resNames = ["out0", "end"]} {
    %0 = extui %arg0 {handshake.bb = 0 : ui32, handshake.name = "extui0"} : <i1> to <i16>
    %1 = ori %0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i16>
    %2 = extsi %1 {handshake.name = "extsi2"} : <i16> to <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %2, %arg2 : <i32>, <>
  }
}

