module {
  func.func @trisolv(%arg0: memref<1000xi32> {handshake.arg_name = "x"}, %arg1: memref<1000000xi32> {handshake.arg_name = "A"}, %arg2: memref<1000xi32> {handshake.arg_name = "c"}) {
    %c0_i32 = arith.constant {handshake.name = "constant0"} 0 : i32
    cf.br ^bb1(%c0_i32 : i32) {handshake.name = "br0"}
  ^bb1(%0: i32):  // 2 preds: ^bb0, ^bb3
    %c0_i32_0 = arith.constant {handshake.name = "constant10"} 0 : i32
    %1 = arith.extui %0 {handshake.name = "extui0"} : i32 to i64
    %2 = arith.index_cast %1 {handshake.name = "index_cast0"} : i64 to index
    %3 = memref.load %arg2[%2] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load0"} : memref<1000xi32>
    %4 = arith.extui %0 {handshake.name = "extui1"} : i32 to i64
    %5 = arith.index_cast %4 {handshake.name = "index_cast1"} : i64 to index
    memref.store %3, %arg0[%5] {handshake.deps = #handshake<deps[{dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 0>, handshake.name = "store1"} : memref<1000xi32>
    %6 = arith.cmpi ugt, %0, %c0_i32_0 {handshake.name = "cmpi0"} : i32
    cf.cond_br %6, ^bb2(%c0_i32_0 : i32), ^bb3 {handshake.name = "cond_br0"}
  ^bb2(%7: i32):  // 2 preds: ^bb1, ^bb2
    %c1_i32 = arith.constant {handshake.name = "constant11"} 1 : i32
    %c9_i64 = arith.constant {handshake.name = "constant12"} 9 : i64
    %c8_i64 = arith.constant {handshake.name = "constant13"} 8 : i64
    %c7_i64 = arith.constant {handshake.name = "constant14"} 7 : i64
    %c6_i64 = arith.constant {handshake.name = "constant15"} 6 : i64
    %c5_i64 = arith.constant {handshake.name = "constant16"} 5 : i64
    %c3_i64 = arith.constant {handshake.name = "constant17"} 3 : i64
    %8 = arith.extui %0 {handshake.name = "extui2"} : i32 to i64
    %9 = arith.index_cast %8 {handshake.name = "index_cast2"} : i64 to index
    %10 = memref.load %arg0[%9] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load2"} : memref<1000xi32>
    %11 = arith.extui %0 {handshake.name = "extui3"} : i32 to i64
    %12 = arith.extui %7 {handshake.name = "extui4"} : i32 to i64
    %13 = arith.shli %11, %c3_i64 {handshake.name = "shli0"} : i64
    %14 = arith.shli %11, %c5_i64 {handshake.name = "shli1"} : i64
    %15 = arith.shli %11, %c6_i64 {handshake.name = "shli2"} : i64
    %16 = arith.addi %14, %15 {handshake.name = "addi4"} : i64
    %17 = arith.addi %13, %16 {handshake.name = "addi5"} : i64
    %18 = arith.shli %11, %c7_i64 {handshake.name = "shli3"} : i64
    %19 = arith.shli %11, %c8_i64 {handshake.name = "shli4"} : i64
    %20 = arith.shli %11, %c9_i64 {handshake.name = "shli5"} : i64
    %21 = arith.addi %19, %20 {handshake.name = "addi6"} : i64
    %22 = arith.addi %18, %21 {handshake.name = "addi7"} : i64
    %23 = arith.addi %17, %22 {handshake.name = "addi8"} : i64
    %24 = arith.addi %23, %12 {handshake.name = "addi0"} : i64
    %25 = arith.index_cast %24 {handshake.name = "index_cast3"} : i64 to index
    %26 = memref.load %arg1[%25] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load3"} : memref<1000000xi32>
    %27 = arith.extui %7 {handshake.name = "extui5"} : i32 to i64
    %28 = arith.index_cast %27 {handshake.name = "index_cast4"} : i64 to index
    %29 = memref.load %arg0[%28] {handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "load4"} : memref<1000xi32>
    %30 = arith.muli %26, %29 {handshake.name = "muli1"} : i32
    %31 = arith.subi %10, %30 {handshake.name = "subi0"} : i32
    %32 = arith.extui %0 {handshake.name = "extui6"} : i32 to i64
    %33 = arith.index_cast %32 {handshake.name = "index_cast5"} : i64 to index
    memref.store %31, %arg0[%33] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load2", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load6", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store8", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 1>, handshake.name = "store5"} : memref<1000xi32>
    %34 = arith.addi %7, %c1_i32 {handshake.name = "addi1"} : i32
    %35 = arith.cmpi ult, %34, %0 {handshake.name = "cmpi1"} : i32
    cf.cond_br %35, ^bb2(%34 : i32), ^bb3 {handshake.name = "cond_br1"}
  ^bb3:  // 2 preds: ^bb1, ^bb2
    %c1000_i32 = arith.constant {handshake.name = "constant18"} 1000 : i32
    %c1_i32_1 = arith.constant {handshake.name = "constant19"} 1 : i32
    %c9_i64_2 = arith.constant {handshake.name = "constant20"} 9 : i64
    %c8_i64_3 = arith.constant {handshake.name = "constant21"} 8 : i64
    %c7_i64_4 = arith.constant {handshake.name = "constant22"} 7 : i64
    %c6_i64_5 = arith.constant {handshake.name = "constant23"} 6 : i64
    %c5_i64_6 = arith.constant {handshake.name = "constant24"} 5 : i64
    %c3_i64_7 = arith.constant {handshake.name = "constant25"} 3 : i64
    %36 = arith.extui %0 {handshake.name = "extui7"} : i32 to i64
    %37 = arith.index_cast %36 {handshake.name = "index_cast6"} : i64 to index
    %38 = memref.load %arg0[%37] {handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "load6"} : memref<1000xi32>
    %39 = arith.extui %0 {handshake.name = "extui8"} : i32 to i64
    %40 = arith.extui %0 {handshake.name = "extui9"} : i32 to i64
    %41 = arith.shli %39, %c3_i64_7 {handshake.name = "shli6"} : i64
    %42 = arith.shli %39, %c5_i64_6 {handshake.name = "shli7"} : i64
    %43 = arith.shli %39, %c6_i64_5 {handshake.name = "shli8"} : i64
    %44 = arith.addi %42, %43 {handshake.name = "addi9"} : i64
    %45 = arith.addi %41, %44 {handshake.name = "addi10"} : i64
    %46 = arith.shli %39, %c7_i64_4 {handshake.name = "shli9"} : i64
    %47 = arith.shli %39, %c8_i64_3 {handshake.name = "shli10"} : i64
    %48 = arith.shli %39, %c9_i64_2 {handshake.name = "shli11"} : i64
    %49 = arith.addi %47, %48 {handshake.name = "addi11"} : i64
    %50 = arith.addi %46, %49 {handshake.name = "addi12"} : i64
    %51 = arith.addi %45, %50 {handshake.name = "addi13"} : i64
    %52 = arith.addi %51, %40 {handshake.name = "addi2"} : i64
    %53 = arith.index_cast %52 {handshake.name = "index_cast7"} : i64 to index
    %54 = memref.load %arg1[%53] {handshake.mem_interface = #handshake.mem_interface<MC>, handshake.name = "load7"} : memref<1000000xi32>
    %55 = arith.divsi %38, %54 {handshake.name = "divsi0"} : i32
    %56 = arith.extui %0 {handshake.name = "extui10"} : i32 to i64
    %57 = arith.index_cast %56 {handshake.name = "index_cast8"} : i64 to index
    memref.store %55, %arg0[%57] {handshake.deps = #handshake<deps[{dstAccess : "store1", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "store5", loopDepth : 0, distance : 0, isActive : true}, {dstAccess : "load4", loopDepth : 0, distance : 0, isActive : true}]>, handshake.mem_interface = #handshake.mem_interface<LSQ: 2>, handshake.name = "store8"} : memref<1000xi32>
    %58 = arith.addi %0, %c1_i32_1 {handshake.name = "addi3"} : i32
    %59 = arith.cmpi ult, %58, %c1000_i32 {handshake.name = "cmpi2"} : i32
    cf.cond_br %59, ^bb1(%58 : i32), ^bb4 {handshake.name = "cond_br2"}
  ^bb4:  // pred: ^bb3
    return {handshake.name = "return0"}
  }
}

