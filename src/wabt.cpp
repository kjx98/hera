/*
 * Copyright 2016-2018 Alex Beregszaszi et al.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include <iostream>

#include "src/interp/binary-reader-interp.h"
#include "src/binary-reader.h"
#include "src/cast.h"
#include "src/feature.h"
#include "src/interp/interp.h"
#include "src/literal.h"
#include "src/option-parser.h"
#include "src/resolve-names.h"
#include "src/stream.h"
#include "src/validator.h"
#include "src/wast-lexer.h"
#include "src/wast-parser.h"

#include "wabt.h"
#include "debugging.h"
#include "eei.h"
#include "exceptions.h"

using namespace std;
using namespace wabt;

namespace hera {

class WabtEthereumInterface : public EthereumInterface {
public:
  explicit WabtEthereumInterface(
    evmc::HostContext& _context,
    bytes_view _code,
    evmc_message const& _msg,
    ExecutionResult & _result,
    bool _meterGas
  ):
    EthereumInterface(_context, _code, _msg, _result, _meterGas)
  {}
  WabtEthereumInterface(const WabtEthereumInterface& ) = default;

  // TODO: improve this design...
  void setWasmMemory(interp::Memory* _wasmMemory) {
    m_wasmMemory = _wasmMemory;
  }

private:
  // These assume that m_wasmMemory was set prior to execution.
  size_t memorySize() const override { return m_wasmMemory->data.size(); }
  void memorySet(size_t offset, uint8_t value) override { m_wasmMemory->data[offset] = static_cast<char>(value); }
  uint8_t memoryGet(size_t offset) override { return static_cast<uint8_t>(m_wasmMemory->data[offset]); }
  uint8_t* memoryPointer(size_t offset, size_t length) override {
    ensureCondition(memorySize() >= (offset + length), InvalidMemoryAccess, "Memory is shorter than requested segment");
    return reinterpret_cast<uint8_t*>(&m_wasmMemory->data[offset]);
  }

  interp::Memory* m_wasmMemory=nullptr;
};

struct envCache_t {
	envCache_t(WabtEthereumInterface* eeInt) : eei_(eeInt) {}
WabtEthereumInterface*	eei_;
interp::Environment env_;
interp::DefinedModule* module_;
};


static inline interp::DefinedModule*
#if HERA_DEBUGGING
instantiation(shared_ptr<envCache_t> envPtr, bytes_view code, const string stateMsg)
#else
instantiation(shared_ptr<envCache_t> envPtr, bytes_view code)
#endif
{
  // Create EEI host module
  // The lifecycle of this pointer is handled by `env`.
  interp::HostModule* hostModule = envPtr->env_.AppendHostModule("ethereum");
  heraAssert(hostModule, "Failed to create host module.");

  hostModule->AppendFuncExport(
    "useGas",
    {{Type::I64}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiUseGas(static_cast<int64_t>(args[0].value.i64));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getAddress",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetAddress(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getExternalBalance",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetExternalBalance(args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockHash",
    {{Type::I64, Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiGetBlockHash(args[0].value.i64, args[1].value.i32));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "call",
    {{Type::I64, Type::I32, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiCall(
        EthereumInterface::EEICallKind::Call,
        static_cast<int64_t>(args[0].value.i64), args[1].value.i32,
        args[2].value.i32, args[3].value.i32, args[4].value.i32
      ));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callDataCopy",
    {{Type::I32, Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiCallDataCopy(args[0].value.i32, args[1].value.i32, args[2].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCallDataSize",
    {{}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiGetCallDataSize());
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callCode",
    {{Type::I64, Type::I32, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiCall(
        EthereumInterface::EEICallKind::CallCode,
        static_cast<int64_t>(args[0].value.i64), args[1].value.i32,
        args[2].value.i32, args[3].value.i32, args[4].value.i32
      ));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callDelegate",
    {{Type::I64, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiCall(
        EthereumInterface::EEICallKind::CallDelegate,
        static_cast<int64_t>(args[0].value.i64), args[1].value.i32, 0,
        args[2].value.i32, args[3].value.i32
      ));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callStatic",
    {{Type::I64, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiCall(
        EthereumInterface::EEICallKind::CallStatic,
        static_cast<int64_t>(args[0].value.i64), args[1].value.i32, 0,
        args[2].value.i32, args[3].value.i32
      ));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "storageStore",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiStorageStore(args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "storageLoad",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiStorageLoad(args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCaller",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetCaller(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCallValue",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetCallValue(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "codeCopy",
    {{Type::I32, Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiCodeCopy(args[0].value.i32, args[1].value.i32, args[2].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCodeSize",
    {{}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiGetCodeSize());
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockCoinbase",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetBlockCoinbase(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "create",
    {{Type::I32, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiCreate(
        args[0].value.i32, args[1].value.i32,
        args[2].value.i32, args[3].value.i32
      ));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockDifficulty",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetBlockDifficulty(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "externalCodeCopy",
    {{Type::I32, Type::I32, Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiExternalCodeCopy(
        args[0].value.i32, args[1].value.i32,
        args[2].value.i32, args[3].value.i32
      );
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getExternalCodeSize",
    {{Type::I32}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiGetExternalCodeSize(args[0].value.i32));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getGasLeft",
    {{}, {Type::I64}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i64(static_cast<uint64_t>(envPtr->eei_->eeiGetGasLeft()));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockGasLimit",
    {{}, {Type::I64}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i64(static_cast<uint64_t>(envPtr->eei_->eeiGetBlockGasLimit()));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getTxGasPrice",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetTxGasPrice(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "log",
    {{Type::I32, Type::I32, Type::I32, Type::I32, Type::I32, Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiLog(
        args[0].value.i32, args[1].value.i32, args[2].value.i32, args[3].value.i32,
        args[4].value.i32, args[5].value.i32, args[6].value.i32
      );
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockNumber",
    {{}, {Type::I64}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i64(static_cast<uint64_t>(envPtr->eei_->eeiGetBlockNumber()));
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getTxOrigin",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiGetTxOrigin(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "finish",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiFinish(args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "revert",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiRevert(args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getReturnDataSize",
    {{}, {Type::I32}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i32(envPtr->eei_->eeiGetReturnDataSize());
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "returnDataCopy",
    {{Type::I32, Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiReturnDataCopy(args[0].value.i32, args[1].value.i32, args[2].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "selfDestruct",
    {{Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->eeiSelfDestruct(args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockTimestamp",
    {{}, {Type::I64}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues& results
    ) {
      results[0].set_i64(static_cast<uint64_t>(envPtr->eei_->eeiGetBlockTimestamp()));
      return interp::Result::Ok;
    }
  );

#if HERA_DEBUGGING
  // Create debug host module
  // The lifecycle of this pointer is handled by `env`.
  hostModule = envPtr->env_.AppendHostModule("debug");
  heraAssert(hostModule, "Failed to create host module.");

  hostModule->AppendFuncExport(
    "printMem",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->debugPrintMem(false, args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "printMemHex",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->debugPrintMem(true, args[0].value.i32, args[1].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "printStorage",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->debugPrintStorage(false, args[0].value.i32);
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "printStorageHex",
    {{Type::I32, Type::I32}, {}},
    [&envPtr](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues& args,
      interp::TypedValues&
    ) {
      envPtr->eei_->debugPrintStorage(true, args[0].value.i32);
      return interp::Result::Ok;
    }
  );
#endif

  // Parse module
  ReadBinaryOptions options(
    Features{},
    nullptr, // debugging stream for loading
    false, // ReadDebugNames
    true, // StopOnFirstError
    true // FailOnCustomSectionError
  );

  Errors errors;
  interp::DefinedModule* module = nullptr;
  Result loadResult = ReadBinaryInterp(
    &envPtr->env_,
    code.data(),
    code.size(),
    options,
    &errors,
    &module
  );

#if HERA_DEBUGGING
  for (auto it = errors.begin(); it != errors.end(); ++it) {
    HERA_DEBUG << stateMsg << it->message << "\n";
  }
#endif

  ensureCondition(Succeeded(loadResult) && module, ContractValidationFailure, "Module failed to load.");
  return module;
}


unique_ptr<WasmEngine> WabtEngine::create()
{
  return unique_ptr<WasmEngine>{new WabtEngine};
}

ExecutionResult WabtEngine::execute(
  evmc::HostContext& context,
  bytes_view code,
  bytes_view state_code,
  evmc_message const& msg,
  bool meterInterfaceGas
) {
  instantiationStarted();
#if HERA_DEBUGGING
  HERA_DEBUG << "Executing with wabt...\n";
#endif

  // Set up the wabt Environment, which includes the Wasm store
  // and the list of modules used for importing/exporting between modules
  //interp::Environment env;

  // Set up interface to eei host functions
  ExecutionResult result;
  shared_ptr<envCache_t>	envPtr;
  interp::DefinedModule* module = nullptr;
  WabtEthereumInterface	interf{context, state_code, msg, result, meterInterfaceGas};
  if (! codeCache.tryGet(msg.destination, envPtr) ) {
	// load, and cache
	envPtr = make_shared<envCache_t>(&interf);
#if HERA_DEBUGGING
	HERA_DEBUG << "instantiation with wabt...\n";
	module = instantiation(envPtr, code, "wabt (execute): ");
#else
	module = instantiation(envPtr, code);
#endif
	if (module != nullptr) {
		envPtr->module_ = module;
		// cache it
		codeCache.insert(msg.destination, envPtr);
	}
  } else {
#if HERA_DEBUGGING
	HERA_DEBUG << "instantiation with wabt(Cached)...\n";
#endif
	module = envPtr->module_;
	envPtr->eei_ = &interf;
  }

  ensureCondition(module, ContractValidationFailure, "Module failed to load or cache.");
  ensureCondition(envPtr->env_.GetMemoryCount() == 1, ContractValidationFailure, "Multiple memory sections exported.");
  ensureCondition(module->GetExport("memory"), ContractValidationFailure, "\"memory\" not found");
  ensureCondition(module->start_func_index == kInvalidIndex, ContractValidationFailure, "Contract contains start function.");

  // Prepare to execute
  interp::Export* mainFunction = module->GetExport("main");
  ensureCondition(mainFunction, ContractValidationFailure, "\"main\" not found");
  ensureCondition(mainFunction->kind == ExternalKind::Func, ContractValidationFailure,  "\"main\" is not a function");
#if HERA_DEBUGGING
	HERA_DEBUG << "prepare wabt Executor...\n";
#endif
  interp::Executor executor(
    &envPtr->env_,
    nullptr, // null for no tracing
    interp::Thread::Options{} // empty for no threads
  );

  // FIXME: really bad design
  envPtr->eei_->setWasmMemory(envPtr->env_.GetMemory(0));

#if HERA_DEBUGGING
	HERA_DEBUG << "interf addr: " << std::hex
		<< (uint64_t)envPtr->eei_ << std::endl;
	HERA_DEBUG << "running wabt RunExport...\n";
#endif
  executionStarted();

  // Execute main
  try {
    interp::ExecResult wabtResult = executor.RunExport(mainFunction, interp::TypedValues{}); // second arg is empty since no args
    // Wrap any non-EEI exception under VMTrap.
    ensureCondition(wabtResult.result == interp::Result::Ok, VMTrap, "The VM invocation had a trap.");
  } catch (EndExecution const&) {
    // This exception is ignored here because we consider it to be a success.
    // It is only a clutch for POSIX style exit()
  }

  executionFinished();
  return result;
}

void WabtEngine::verifyContract(bytes_view code) {
  // Set up the wabt Environment, which includes the Wasm store
  // and the list of modules used for importing/exporting between modules
  interp::Environment env;

  // Create EEI host module
  // The lifecycle of this pointer is handled by `env`.
  interp::HostModule* hostModule = env.AppendHostModule("ethereum");
  heraAssert(hostModule, "Failed to create host module.");

  hostModule->AppendFuncExport(
    "useGas",
    {{Type::I64}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getAddress",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getExternalBalance",
    {{Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockHash",
    {{Type::I64, Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "call",
    {{Type::I64, Type::I32, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callDataCopy",
    {{Type::I32, Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCallDataSize",
    {{}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callCode",
    {{Type::I64, Type::I32, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callDelegate",
    {{Type::I64, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "callStatic",
    {{Type::I64, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "storageStore",
    {{Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "storageLoad",
    {{Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCaller",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCallValue",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "codeCopy",
    {{Type::I32, Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getCodeSize",
    {{}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockCoinbase",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "create",
    {{Type::I32, Type::I32, Type::I32, Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockDifficulty",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "externalCodeCopy",
    {{Type::I32, Type::I32, Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getExternalCodeSize",
    {{Type::I32}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getGasLeft",
    {{}, {Type::I64}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockGasLimit",
    {{}, {Type::I64}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getTxGasPrice",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "log",
    {{Type::I32, Type::I32, Type::I32, Type::I32, Type::I32, Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockNumber",
    {{}, {Type::I64}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getTxOrigin",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "finish",
    {{Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "revert",
    {{Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getReturnDataSize",
    {{}, {Type::I32}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "returnDataCopy",
    {{Type::I32, Type::I32, Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "selfDestruct",
    {{Type::I32}, {}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "getBlockTimestamp",
    {{}, {Type::I64}},
    [](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

#if HERA_DEBUGGING
  // Create debug host module
  // The lifecycle of this pointer is handled by `env`.
  hostModule = env.AppendHostModule("debug");
  heraAssert(hostModule, "Failed to create host module.");

  hostModule->AppendFuncExport(
    "printMem",
    {{Type::I32, Type::I32}, {}},
    [&](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "printMemHex",
    {{Type::I32, Type::I32}, {}},
    [&](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "printStorage",
    {{Type::I32, Type::I32}, {}},
    [&](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );

  hostModule->AppendFuncExport(
    "printStorageHex",
    {{Type::I32, Type::I32}, {}},
    [&](
      const interp::HostFunc*,
      const interp::FuncSignature*,
      const interp::TypedValues&,
      interp::TypedValues&
    ) {
      return interp::Result::Ok;
    }
  );
#endif

  // Parse module
  ReadBinaryOptions options(
    Features{},
    nullptr, // debugging stream for loading
    false, // ReadDebugNames
    true, // StopOnFirstError
    true // FailOnCustomSectionError
  );

  Errors errors;
  interp::DefinedModule* module = nullptr;
  Result loadResult = ReadBinaryInterp(
    &env,
    code.data(),
    code.size(),
    options,
    &errors,
    &module
  );

#if HERA_DEBUGGING
  for (auto it = errors.begin(); it != errors.end(); ++it) {
    HERA_DEBUG << "wabt (verifyContract): " << it->message << "\n";
  }
#endif

  ensureCondition(Succeeded(loadResult) && module, ContractValidationFailure, "Module failed to load.");
  ensureCondition(env.GetMemoryCount() == 1, ContractValidationFailure, "Multiple memory sections exported.");
  ensureCondition(module->GetExport("memory"), ContractValidationFailure, "\"memory\" not found");
  ensureCondition(module->start_func_index == kInvalidIndex, ContractValidationFailure, "Contract contains start function.");

  interp::Export* mainFunction = module->GetExport("main");
  ensureCondition(mainFunction, ContractValidationFailure, "\"main\" not found");
  ensureCondition(mainFunction->kind == ExternalKind::Func, ContractValidationFailure,  "\"main\" is not a function");
};

}
