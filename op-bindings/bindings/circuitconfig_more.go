// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package bindings

import (
	"encoding/json"

	"github.com/ethereum-optimism/optimism/op-bindings/solc"
)

const CircuitConfigStorageLayoutJSON = "{\"storage\":null,\"types\":{}}"

var CircuitConfigStorageLayout = new(solc.StorageLayout)

var CircuitConfigDeployedBin = "0x6080604052600080fdfea164736f6c634300080f000a"

func init() {
	if err := json.Unmarshal([]byte(CircuitConfigStorageLayoutJSON), CircuitConfigStorageLayout); err != nil {
		panic(err)
	}

	layouts["CircuitConfig"] = CircuitConfigStorageLayout
	deployedBytecodes["CircuitConfig"] = CircuitConfigDeployedBin
}
