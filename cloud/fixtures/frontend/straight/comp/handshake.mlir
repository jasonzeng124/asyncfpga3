module {
  handshake.func @straight(%arg0: !handshake.channel<i32>, %arg1: !handshake.channel<i32>, %arg2: !handshake.control<>, ...) -> (!handshake.channel<i32>, !handshake.control<>) attributes {argNames = ["a", "b", "start"], resNames = ["out0", "end"]} {
    %0 = source {handshake.bb = 0 : ui32, handshake.name = "source0"} : <>
    %1 = constant %0 {handshake.bb = 0 : ui32, handshake.name = "constant0", value = 7 : i32} : <>, <i32>
    %2 = source {handshake.bb = 0 : ui32, handshake.name = "source1"} : <>
    %3 = constant %2 {handshake.bb = 0 : ui32, handshake.name = "constant1", value = 3 : i32} : <>, <i32>
    %4 = source {handshake.bb = 0 : ui32, handshake.name = "source2"} : <>
    %5 = constant %4 {handshake.bb = 0 : ui32, handshake.name = "constant2", value = 2 : i32} : <>, <i32>
    %6 = source {handshake.bb = 0 : ui32, handshake.name = "source3"} : <>
    %7 = constant %6 {handshake.bb = 0 : ui32, handshake.name = "constant3", value = 11 : i32} : <>, <i32>
    %8 = source {handshake.bb = 0 : ui32, handshake.name = "source4"} : <>
    %9 = constant %8 {handshake.bb = 0 : ui32, handshake.name = "constant4", value = -1640531527 : i32} : <>, <i32>
    %10 = addi %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "addi0"} : <i32>
    %11 = subi %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "subi0"} : <i32>
    %12 = shli %11, %1 {handshake.bb = 0 : ui32, handshake.name = "shli0"} : <i32>
    %13 = xori %10, %12 {handshake.bb = 0 : ui32, handshake.name = "xori0"} : <i32>
    %14 = shrui %arg0, %3 {handshake.bb = 0 : ui32, handshake.name = "shrui0"} : <i32>
    %15 = addi %13, %14 {handshake.bb = 0 : ui32, handshake.name = "addi1"} : <i32>
    %16 = shli %arg1, %5 {handshake.bb = 0 : ui32, handshake.name = "shli1"} : <i32>
    %17 = subi %15, %16 {handshake.bb = 0 : ui32, handshake.name = "subi1"} : <i32>
    %18 = shrui %17, %7 {handshake.bb = 0 : ui32, handshake.name = "shrui1"} : <i32>
    %19 = xori %17, %18 {handshake.bb = 0 : ui32, handshake.name = "xori1"} : <i32>
    %20 = addi %19, %9 {handshake.bb = 0 : ui32, handshake.name = "addi2"} : <i32>
    %21 = andi %10, %11 {handshake.bb = 0 : ui32, handshake.name = "andi0"} : <i32>
    %22 = subi %20, %21 {handshake.bb = 0 : ui32, handshake.name = "subi2"} : <i32>
    %23 = ori %arg0, %arg1 {handshake.bb = 0 : ui32, handshake.name = "ori0"} : <i32>
    %24 = addi %22, %23 {handshake.bb = 0 : ui32, handshake.name = "addi3"} : <i32>
    end {handshake.bb = 0 : ui32, handshake.name = "end0"} %24, %arg2 : <i32>, <>
  }
}

