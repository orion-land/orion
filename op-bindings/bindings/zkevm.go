// Code generated - DO NOT EDIT.
// This file is a generated binding and any manual changes will be lost.

package bindings

import (
	"errors"
	"math/big"
	"strings"

	ethereum "github.com/ethereum/go-ethereum"
	"github.com/ethereum/go-ethereum/accounts/abi"
	"github.com/ethereum/go-ethereum/accounts/abi/bind"
	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/types"
	"github.com/ethereum/go-ethereum/event"
)

// Reference imports to suppress errors if they are not otherwise used.
var (
	_ = errors.New
	_ = big.NewInt
	_ = strings.NewReader
	_ = ethereum.NotFound
	_ = bind.Bind
	_ = common.Big1
	_ = types.BloomLookup
	_ = event.NewSubscription
	_ = abi.ConvertType
)

// ZKEVMBatchData is an auto generated low-level Go binding around an user-defined struct.
type ZKEVMBatchData struct {
	BlockNumber  uint64
	Transactions []byte
	BlockWitnes  []byte
	PreStateRoot [32]byte
	WithdrawRoot [32]byte
	Signature    ZKEVMBatchSignature
}

// ZKEVMBatchSignature is an auto generated low-level Go binding around an user-defined struct.
type ZKEVMBatchSignature struct {
	Signers   [][]byte
	Signature []byte
}

// ZKEVMMetaData contains all meta data concerning the ZKEVM contract.
var ZKEVMMetaData = &bind.MetaData{
	ABI: "[{\"inputs\":[{\"internalType\":\"address\",\"name\":\"_submitter\",\"type\":\"address\"},{\"internalType\":\"address\",\"name\":\"_challenger\",\"type\":\"address\"}],\"stateMutability\":\"nonpayable\",\"type\":\"constructor\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":true,\"internalType\":\"uint256\",\"name\":\"batchIndex\",\"type\":\"uint256\"},{\"indexed\":false,\"internalType\":\"address\",\"name\":\"winner\",\"type\":\"address\"},{\"indexed\":false,\"internalType\":\"string\",\"name\":\"res\",\"type\":\"string\"}],\"name\":\"ChallengeRes\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":true,\"internalType\":\"uint256\",\"name\":\"batchIndex\",\"type\":\"uint256\"},{\"indexed\":false,\"internalType\":\"address\",\"name\":\"challenger\",\"type\":\"address\"},{\"indexed\":false,\"internalType\":\"uint256\",\"name\":\"challengeDeposit\",\"type\":\"uint256\"}],\"name\":\"ChallengeState\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":false,\"internalType\":\"uint8\",\"name\":\"version\",\"type\":\"uint8\"}],\"name\":\"Initialized\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":true,\"internalType\":\"address\",\"name\":\"previousOwner\",\"type\":\"address\"},{\"indexed\":true,\"internalType\":\"address\",\"name\":\"newOwner\",\"type\":\"address\"}],\"name\":\"OwnershipTransferred\",\"type\":\"event\"},{\"anonymous\":false,\"inputs\":[{\"indexed\":true,\"internalType\":\"uint64\",\"name\":\"numBatch\",\"type\":\"uint64\"},{\"indexed\":false,\"internalType\":\"uint64\",\"name\":\"l2Num\",\"type\":\"uint64\"}],\"name\":\"SubmitBatches\",\"type\":\"event\"},{\"inputs\":[],\"name\":\"FINALIZATION_PERIOD_SECONDS\",\"outputs\":[{\"internalType\":\"uint256\",\"name\":\"\",\"type\":\"uint256\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"MIN_DEPOSIT\",\"outputs\":[{\"internalType\":\"uint256\",\"name\":\"\",\"type\":\"uint256\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"PORTAL\",\"outputs\":[{\"internalType\":\"contractOptimismPortal\",\"name\":\"\",\"type\":\"address\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"PROOF_WINDOW\",\"outputs\":[{\"internalType\":\"uint256\",\"name\":\"\",\"type\":\"uint256\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"batchIndex\",\"type\":\"uint64\"}],\"name\":\"challengeState\",\"outputs\":[],\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"challenger\",\"outputs\":[{\"internalType\":\"address\",\"name\":\"\",\"type\":\"address\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"\",\"type\":\"uint64\"}],\"name\":\"challenges\",\"outputs\":[{\"internalType\":\"uint64\",\"name\":\"batchIndex\",\"type\":\"uint64\"},{\"internalType\":\"address\",\"name\":\"challenger\",\"type\":\"address\"},{\"internalType\":\"uint256\",\"name\":\"challengeDeposit\",\"type\":\"uint256\"},{\"internalType\":\"uint256\",\"name\":\"startTime\",\"type\":\"uint256\"},{\"internalType\":\"bool\",\"name\":\"finished\",\"type\":\"bool\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"batchIndex\",\"type\":\"uint64\"}],\"name\":\"confirmBatch\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"\",\"type\":\"uint64\"}],\"name\":\"confirmBatchIndex\",\"outputs\":[{\"internalType\":\"bool\",\"name\":\"\",\"type\":\"bool\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"address\",\"name\":\"\",\"type\":\"address\"}],\"name\":\"deposits\",\"outputs\":[{\"internalType\":\"uint256\",\"name\":\"\",\"type\":\"uint256\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"address\",\"name\":\"_submitter\",\"type\":\"address\"},{\"internalType\":\"address\",\"name\":\"_challenger\",\"type\":\"address\"}],\"name\":\"initialize\",\"outputs\":[],\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"batchIndex\",\"type\":\"uint64\"}],\"name\":\"isBatchInChallenge\",\"outputs\":[{\"internalType\":\"bool\",\"name\":\"\",\"type\":\"bool\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"address\",\"name\":\"addr\",\"type\":\"address\"}],\"name\":\"isStaked\",\"outputs\":[{\"internalType\":\"bool\",\"name\":\"\",\"type\":\"bool\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"address\",\"name\":\"user\",\"type\":\"address\"}],\"name\":\"isUserInChallenge\",\"outputs\":[{\"internalType\":\"bool\",\"name\":\"\",\"type\":\"bool\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"lastBatchSequenced\",\"outputs\":[{\"internalType\":\"uint64\",\"name\":\"\",\"type\":\"uint64\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"lastL2BlockNumber\",\"outputs\":[{\"internalType\":\"uint64\",\"name\":\"\",\"type\":\"uint64\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"owner\",\"outputs\":[{\"internalType\":\"address\",\"name\":\"\",\"type\":\"address\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"batchIndex\",\"type\":\"uint64\"},{\"internalType\":\"bytes\",\"name\":\"proof\",\"type\":\"bytes\"}],\"name\":\"proveState\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"renounceOwnership\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"contractOptimismPortal\",\"name\":\"_portal\",\"type\":\"address\"}],\"name\":\"setPortal\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"stake\",\"outputs\":[],\"stateMutability\":\"payable\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint64\",\"name\":\"\",\"type\":\"uint64\"}],\"name\":\"storageBatchs\",\"outputs\":[{\"internalType\":\"uint64\",\"name\":\"blockNumber\",\"type\":\"uint64\"},{\"internalType\":\"bytes32\",\"name\":\"withdrawRoot\",\"type\":\"bytes32\"},{\"internalType\":\"bytes32\",\"name\":\"commitment\",\"type\":\"bytes32\"},{\"internalType\":\"bytes32\",\"name\":\"stateRoot\",\"type\":\"bytes32\"},{\"internalType\":\"uint256\",\"name\":\"originTimestamp\",\"type\":\"uint256\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"components\":[{\"internalType\":\"uint64\",\"name\":\"blockNumber\",\"type\":\"uint64\"},{\"internalType\":\"bytes\",\"name\":\"transactions\",\"type\":\"bytes\"},{\"internalType\":\"bytes\",\"name\":\"blockWitnes\",\"type\":\"bytes\"},{\"internalType\":\"bytes32\",\"name\":\"preStateRoot\",\"type\":\"bytes32\"},{\"internalType\":\"bytes32\",\"name\":\"withdrawRoot\",\"type\":\"bytes32\"},{\"components\":[{\"internalType\":\"bytes[]\",\"name\":\"signers\",\"type\":\"bytes[]\"},{\"internalType\":\"bytes\",\"name\":\"signature\",\"type\":\"bytes\"}],\"internalType\":\"structZKEVM.BatchSignature\",\"name\":\"signature\",\"type\":\"tuple\"}],\"internalType\":\"structZKEVM.BatchData[]\",\"name\":\"batches\",\"type\":\"tuple[]\"}],\"name\":\"submitBatches\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[],\"name\":\"submitter\",\"outputs\":[{\"internalType\":\"address\",\"name\":\"\",\"type\":\"address\"}],\"stateMutability\":\"view\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"address\",\"name\":\"newOwner\",\"type\":\"address\"}],\"name\":\"transferOwnership\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"uint256\",\"name\":\"amount\",\"type\":\"uint256\"}],\"name\":\"withdraw\",\"outputs\":[],\"stateMutability\":\"nonpayable\",\"type\":\"function\"},{\"inputs\":[{\"internalType\":\"bytes32\",\"name\":\"\",\"type\":\"bytes32\"}],\"name\":\"withdrawRoots\",\"outputs\":[{\"internalType\":\"uint256\",\"name\":\"\",\"type\":\"uint256\"}],\"stateMutability\":\"view\",\"type\":\"function\"}]",
	Bin: "0x60806040523480156200001157600080fd5b5060405162002b6238038062002b6283398101604081905262000034916200031e565b62000040828262000048565b50506200037d565b600054610100900460ff1615808015620000695750600054600160ff909116105b806200009957506200008630620001d760201b62001dcc1760201c565b15801562000099575060005460ff166001145b620001025760405162461bcd60e51b815260206004820152602e60248201527f496e697469616c697a61626c653a20636f6e747261637420697320616c72656160448201526d191e481a5b9a5d1a585b1a5e995960921b60648201526084015b60405180910390fd5b6000805460ff19166001179055801562000126576000805461ff0019166101001790555b62000130620001e6565b60678054606680546001600160a01b0319166001600160a01b038781169182179092556001600160e01b031990921690851617909155600090815260696020526040812080543492906200018690849062000356565b90915550508015620001d2576000805461ff0019169055604051600181527f7f26b83ff96e1f2b6a682f133852f6798a09c465da95921460cefb38474024989060200160405180910390a15b505050565b6001600160a01b03163b151590565b600054610100900460ff16620002425760405162461bcd60e51b815260206004820152602b602482015260008051602062002b4283398151915260448201526a6e697469616c697a696e6760a81b6064820152608401620000f9565b6200024c6200024e565b565b600054610100900460ff16620002aa5760405162461bcd60e51b815260206004820152602b602482015260008051602062002b4283398151915260448201526a6e697469616c697a696e6760a81b6064820152608401620000f9565b6200024c33603380546001600160a01b038381166001600160a01b0319831681179093556040519116919082907f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e090600090a35050565b80516001600160a01b03811681146200031957600080fd5b919050565b600080604083850312156200033257600080fd5b6200033d8362000301565b91506200034d6020840162000301565b90509250929050565b600082198211156200037857634e487b7160e01b600052601160045260246000fd5b500190565b6127b5806200038d6000396000f3fe6080604052600436106101ac5760003560e01c80638ad9e18e116100ec578063e291c2f51161008a578063f2fde38b11610064578063f2fde38b1461062a578063f4daa2911461064a578063f71b51f314610661578063fc7e286d1461069157600080fd5b8063e291c2f51461056c578063eb1ec18f146105f4578063f02deda11461060957600080fd5b80638dc45d9a116100c65780638dc45d9a14610447578063acc1245a14610474578063c7ab203914610494578063e1e158a51461055057600080fd5b80638ad9e18e146103ce5780638d644bb7146104095780638da5cb5b1461041c57600080fd5b8063485cc95511610159578063534db0e211610133578063534db0e21461032757806359ef1120146103545780636177fd1814610374578063715018a6146103b957600080fd5b8063485cc955146102d45780634b21f578146102e75780634ff561921461030757600080fd5b80632e1a7d4d1161018a5780632e1a7d4d1461025a5780633a4b66f11461027a578063423fa8561461028257600080fd5b8063032ecb38146101b15780630ff754ea146101d357806323ec85181461022a575b600080fd5b3480156101bd57600080fd5b506101d16101cc3660046123b4565b6106be565b005b3480156101df57600080fd5b506065546102009073ffffffffffffffffffffffffffffffffffffffff1681565b60405173ffffffffffffffffffffffffffffffffffffffff90911681526020015b60405180910390f35b34801561023657600080fd5b5061024a6102453660046123f1565b6107d8565b6040519015158152602001610221565b34801561026657600080fd5b506101d161027536600461240e565b610953565b6101d1610b5a565b34801561028e57600080fd5b506067546102bb9074010000000000000000000000000000000000000000900467ffffffffffffffff1681565b60405167ffffffffffffffff9091168152602001610221565b6101d16102e2366004612427565b610d3d565b3480156102f357600080fd5b506101d1610302366004612460565b610f66565b34801561031357600080fd5b506101d16103223660046123f1565b611531565b34801561033357600080fd5b506067546102009073ffffffffffffffffffffffffffffffffffffffff1681565b34801561036057600080fd5b506101d161036f3660046124d5565b611580565b34801561038057600080fd5b5061024a61038f3660046123f1565b73ffffffffffffffffffffffffffffffffffffffff16600090815260696020526040902054151590565b3480156103c557600080fd5b506101d1611842565b3480156103da57600080fd5b506103fb6103e936600461240e565b606a6020526000908152604090205481565b604051908152602001610221565b6101d16104173660046123b4565b611856565b34801561042857600080fd5b5060335473ffffffffffffffffffffffffffffffffffffffff16610200565b34801561045357600080fd5b506066546102009073ffffffffffffffffffffffffffffffffffffffff1681565b34801561048057600080fd5b5061024a61048f3660046123b4565b611ca8565b3480156104a057600080fd5b506105066104af3660046123b4565b606d60205260009081526040902080546001820154600283015460039093015467ffffffffffffffff8316936801000000000000000090930473ffffffffffffffffffffffffffffffffffffffff16929060ff1685565b6040805167ffffffffffffffff909616865273ffffffffffffffffffffffffffffffffffffffff90941660208601529284019190915260608301521515608082015260a001610221565b34801561055c57600080fd5b506103fb670de0b6b3a764000081565b34801561057857600080fd5b506105c16105873660046123b4565b606b602052600090815260409020805460018201546002830154600384015460049094015467ffffffffffffffff90931693919290919085565b6040805167ffffffffffffffff90961686526020860194909452928401919091526060830152608082015260a001610221565b34801561060057600080fd5b506103fb606481565b34801561061557600080fd5b506068546102bb9067ffffffffffffffff1681565b34801561063657600080fd5b506101d16106453660046123f1565b611d15565b34801561065657600080fd5b506103fb620186a081565b34801561066d57600080fd5b5061024a61067c3660046123b4565b606c6020526000908152604090205460ff1681565b34801561069d57600080fd5b506103fb6106ac3660046123f1565b60696020526000908152604090205481565b6106c781611ca8565b156106d157600080fd5b67ffffffffffffffff81166000908152606b602052604081206004015442906106fe90620186a090612587565b1190508015610794576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152603060248201527f43616e6e6f7420636f6e6669726d20626174636820696e73696465207468652060448201527f6368616c6c656e67652077696e646f770000000000000000000000000000000060648201526084015b60405180910390fd5b5067ffffffffffffffff166000908152606c6020526040902080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00166001179055565b60675460009074010000000000000000000000000000000000000000900467ffffffffffffffff16810361080e57506000919050565b60665473ffffffffffffffffffffffffffffffffffffffff9081169083160361088d57606754606c906000906108689060019074010000000000000000000000000000000000000000900467ffffffffffffffff1661259f565b67ffffffffffffffff16815260208101919091526040016000205460ff161592915050565b60005b60675467ffffffffffffffff740100000000000000000000000000000000000000009091048116908216101561094a5767ffffffffffffffff81166000908152606d602052604090205473ffffffffffffffffffffffffffffffffffffffff848116680100000000000000009092041614801561092a575067ffffffffffffffff81166000908152606d602052604090206003015460ff16155b156109385750600192915050565b80610942816125c8565b915050610890565b50506000919050565b61095c336107d8565b156109c3576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601460248201527f5573657220697320696e206368616c6c656e6765000000000000000000000000604482015260640161078b565b33600090815260696020526040902054816109dd57600080fd5b81816109f1670de0b6b3a764000083612587565b1115610b1b5760665473ffffffffffffffffffffffffffffffffffffffff1633148015610a41575060675474010000000000000000000000000000000000000000900467ffffffffffffffff1615155b15610b1b5760675474010000000000000000000000000000000000000000900467ffffffffffffffff166000908152606b60205260409020600401544290610a8d90620186a090612587565b1115610b1b576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602960248201527f7375626d69747465722073686f756c64207761697420626174636820746f206260448201527f6520636f6e6669726d0000000000000000000000000000000000000000000000606482015260840161078b565b81831115610b265750805b3360009081526069602052604081208054859290610b459084906125ef565b90915550610b5590503382611de8565b505050565b60665473ffffffffffffffffffffffffffffffffffffffff16610bd9576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601e60248201527f5375626d69747465722063616e6e6f7420626520616464726573732830290000604482015260640161078b565b60665473ffffffffffffffffffffffffffffffffffffffff163314610c5a576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601460248201527f43616c6c6572206e6f74207375626d6974746572000000000000000000000000604482015260640161078b565b60665473ffffffffffffffffffffffffffffffffffffffff16600090815260696020526040902054670de0b6b3a764000090610c97903490612587565b1015610cff576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601a60248201527f446f206e6f74206861766520656e6f756768206465706f736974000000000000604482015260640161078b565b60665473ffffffffffffffffffffffffffffffffffffffff1660009081526069602052604081208054349290610d36908490612587565b9091555050565b600054610100900460ff1615808015610d5d5750600054600160ff909116105b80610d775750303b158015610d77575060005460ff166001145b610e03576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602e60248201527f496e697469616c697a61626c653a20636f6e747261637420697320616c72656160448201527f647920696e697469616c697a6564000000000000000000000000000000000000606482015260840161078b565b600080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff001660011790558015610e6157600080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff166101001790555b610e69611e94565b60678054606680547fffffffffffffffffffffffff00000000000000000000000000000000000000001673ffffffffffffffffffffffffffffffffffffffff8781169182179092557fffffffff000000000000000000000000000000000000000000000000000000009092169085161790915560009081526069602052604081208054349290610efa908490612587565b90915550508015610b5557600080547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00ff169055604051600181527f7f26b83ff96e1f2b6a682f133852f6798a09c465da95921460cefb38474024989060200160405180910390a1505050565b60665473ffffffffffffffffffffffffffffffffffffffff16610fe5576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601e60248201527f5375626d69747465722063616e6e6f7420626520616464726573732830290000604482015260640161078b565b60665473ffffffffffffffffffffffffffffffffffffffff163314611066576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601460248201527f43616c6c6572206e6f74207375626d6974746572000000000000000000000000604482015260640161078b565b60665473ffffffffffffffffffffffffffffffffffffffff16600090815260696020526040902054670de0b6b3a764000011156110ff576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601b60248201527f496e73756666696369656e74207374616b696e6720616d6f756e740000000000604482015260640161078b565b606754819074010000000000000000000000000000000000000000900467ffffffffffffffff1660005b8281101561141857606361f61860008061114283611f33565b67ffffffffffffffff88166000908152606b6020526040902060030154919350915089898781811061117657611176612606565b90506020028101906111889190612635565b60600135146111f3576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601c60248201527f5072657669657720737461746520726f6f74206e6f7420657175616c00000000604482015260640161078b565b60006112388383878d8d8b81811061120d5761120d612606565b905060200281019061121f9190612635565b61122d906040810190612673565b506060949350505050565b905060006112a88b8b8981811061125157611251612606565b90506020028101906112639190612635565b611271906040810190612673565b8d8d8b81811061128357611283612606565b90506020028101906112959190612635565b6112a39060208101906123b4565b611fc6565b9050600060208351026020840120905042606a60008e8e8c8181106112cf576112cf612606565b90506020028101906112e19190612635565b608001358152602001908152602001600020819055506040518060a001604052808d8d8b81811061131457611314612606565b90506020028101906113269190612635565b6113349060208101906123b4565b67ffffffffffffffff1681526020018d8d8b81811061135557611355612606565b90506020028101906113679190612635565b6080908101358252602080830185905260408084018790524260609485015267ffffffffffffffff8e81166000908152606b8452829020865181547fffffffffffffffffffffffffffffffffffffffffffffffff000000000000000016921691909117815591850151600183015584015160028201559183015160038301559190910151600490910155886113fb816125c8565b995050505050505050508080611410906126df565b915050611129565b50606780547fffffffff0000000000000000ffffffffffffffffffffffffffffffffffffffff167401000000000000000000000000000000000000000067ffffffffffffffff84160217905583836114716001856125ef565b81811061148057611480612606565b90506020028101906114929190612635565b6114a09060208101906123b4565b606880547fffffffffffffffffffffffffffffffffffffffffffffffff00000000000000001667ffffffffffffffff928316908117909155606754604051918252740100000000000000000000000000000000000000009004909116907faff2dd67e4faff27d6d11dbdc2eda3379b944ad1b67b973265a60efd9cd08ac9906020015b60405180910390a250505050565b611539611fd0565b606580547fffffffffffffffffffffffff00000000000000000000000000000000000000001673ffffffffffffffffffffffffffffffffffffffff92909216919091179055565b67ffffffffffffffff83166000908152606d602052604090205468010000000000000000900473ffffffffffffffffffffffffffffffffffffffff166115c557600080fd5b67ffffffffffffffff83166000908152606d602052604090206003015460ff161561164c576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601a60248201527f4368616c6c656e676520616c72656164792066696e6973686564000000000000604482015260640161078b565b67ffffffffffffffff83166000908152606d6020526040812060020154429061167790606490612587565b119050806116c3576116be846040518060400160405280600781526020017f74696d656f757400000000000000000000000000000000000000000000000000815250612051565b6117f9565b8161172a576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600d60248201527f496e76616c69642070726f6f6600000000000000000000000000000000000000604482015260640161078b565b67ffffffffffffffff84166000908152606b6020526040902060020154611754908490849061214e565b6117ba576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600c60248201527f50726f7665206661696c65640000000000000000000000000000000000000000604482015260640161078b565b6117f9846040518060400160405280600d81526020017f70726f7665207375636365737300000000000000000000000000000000000000815250612169565b50505067ffffffffffffffff166000908152606d6020526040902060030180547fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00166001179055565b61184a611fd0565b6118546000612266565b565b60675473ffffffffffffffffffffffffffffffffffffffff166118d5576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601f60248201527f4368616c6c656e6765722063616e6e6f74206265206164647265737328302900604482015260640161078b565b60675473ffffffffffffffffffffffffffffffffffffffff163314611956576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601560248201527f43616c6c6572206e6f74206368616c6c656e6765720000000000000000000000604482015260640161078b565b67ffffffffffffffff81166000908152606b602052604081206004015490036119db576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600f60248201527f4261746368206e6f742065786973740000000000000000000000000000000000604482015260640161078b565b67ffffffffffffffff81166000908152606d602052604090205468010000000000000000900473ffffffffffffffffffffffffffffffffffffffff1615611a7e576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152601560248201527f416c726561647920686173206368616c6c656e67650000000000000000000000604482015260640161078b565b67ffffffffffffffff81166000908152606b60205260408120600401544290611aab90620186a090612587565b11905080611b3b576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152603360248201527f43616e6e6f74206368616c6c656e6765206261746368206f757473696465207460448201527f6865206368616c6c656e67652077696e646f7700000000000000000000000000606482015260840161078b565b670de0b6b3a7640000341015611b5057600080fd5b60675473ffffffffffffffffffffffffffffffffffffffff1660009081526069602052604081208054349290611b87908490612587565b90915550506040805160a08101825267ffffffffffffffff848116808352336020808501828152348688018181524260608901908152600060808a01818152888252606d8752908b902099518a54955173ffffffffffffffffffffffffffffffffffffffff1668010000000000000000027fffffffff00000000000000000000000000000000000000000000000000000000909616991698909817939093178855516001880155905160028701559351600390950180549515157fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0090961695909517909455845190815292830191909152917fff4bd2fd14b0670e131544fdc1e7c53f06371ccac4a3a8e0445a93d02d68fb05910160405180910390a25050565b67ffffffffffffffff81166000908152606d602052604081205468010000000000000000900473ffffffffffffffffffffffffffffffffffffffff1615801590611d0f575067ffffffffffffffff82166000908152606d602052604090206003015460ff16155b92915050565b611d1d611fd0565b73ffffffffffffffffffffffffffffffffffffffff8116611dc0576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602660248201527f4f776e61626c653a206e6577206f776e657220697320746865207a65726f206160448201527f6464726573730000000000000000000000000000000000000000000000000000606482015260840161078b565b611dc981612266565b50565b73ffffffffffffffffffffffffffffffffffffffff163b151590565b6000611e05835a84604051806020016040528060008152506122dd565b905080610b55576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602360248201527f5374616e646172644272696467653a20455448207472616e736665722066616960448201527f6c65640000000000000000000000000000000000000000000000000000000000606482015260840161078b565b600054610100900460ff16611f2b576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602b60248201527f496e697469616c697a61626c653a20636f6e7472616374206973206e6f74206960448201527f6e697469616c697a696e67000000000000000000000000000000000000000000606482015260840161078b565b6118546122f7565b60008061f6188311611f4c575060039261290492509050565b620493e08311611f645750600e926201107692509050565b6040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152600e60248201527f434952435549545f434f4e464947000000000000000000000000000000000000604482015260640161078b565b60005b9392505050565b60335473ffffffffffffffffffffffffffffffffffffffff163314611854576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820181905260248201527f4f776e61626c653a2063616c6c6572206973206e6f7420746865206f776e6572604482015260640161078b565b67ffffffffffffffff82166000908152606d602090815260408083205460665473ffffffffffffffffffffffffffffffffffffffff9081168552606990935290832080546801000000000000000090920490921692670de0b6b3a764000092916120bc9084906125ef565b909155505073ffffffffffffffffffffffffffffffffffffffff811660009081526069602052604081208054670de0b6b3a764000092906120fe908490612587565b925050819055508267ffffffffffffffff167fe70d3820e244d5f71d1a6395db24f3460e8dca966edc1fd3625b6292880a877a8284604051612141929190612717565b60405180910390a2505050565b600082810361215f57506000611fc9565b5060019392505050565b67ffffffffffffffff82166000908152606d6020908152604080832080546001909101546801000000000000000090910473ffffffffffffffffffffffffffffffffffffffff1680855260699093529083208054929391928392906121cf9084906125ef565b909155505060665473ffffffffffffffffffffffffffffffffffffffff166000908152606960205260408120805483929061220b908490612587565b909155505060665460405167ffffffffffffffff8616917fe70d3820e244d5f71d1a6395db24f3460e8dca966edc1fd3625b6292880a877a916115239173ffffffffffffffffffffffffffffffffffffffff16908790612717565b6033805473ffffffffffffffffffffffffffffffffffffffff8381167fffffffffffffffffffffffff0000000000000000000000000000000000000000831681179093556040519116919082907f8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e090600090a35050565b600080600080845160208601878a8af19695505050505050565b600054610100900460ff1661238e576040517f08c379a000000000000000000000000000000000000000000000000000000000815260206004820152602b60248201527f496e697469616c697a61626c653a20636f6e7472616374206973206e6f74206960448201527f6e697469616c697a696e67000000000000000000000000000000000000000000606482015260840161078b565b61185433612266565b803567ffffffffffffffff811681146123af57600080fd5b919050565b6000602082840312156123c657600080fd5b611fc982612397565b73ffffffffffffffffffffffffffffffffffffffff81168114611dc957600080fd5b60006020828403121561240357600080fd5b8135611fc9816123cf565b60006020828403121561242057600080fd5b5035919050565b6000806040838503121561243a57600080fd5b8235612445816123cf565b91506020830135612455816123cf565b809150509250929050565b6000806020838503121561247357600080fd5b823567ffffffffffffffff8082111561248b57600080fd5b818501915085601f83011261249f57600080fd5b8135818111156124ae57600080fd5b8660208260051b85010111156124c357600080fd5b60209290920196919550909350505050565b6000806000604084860312156124ea57600080fd5b6124f384612397565b9250602084013567ffffffffffffffff8082111561251057600080fd5b818601915086601f83011261252457600080fd5b81358181111561253357600080fd5b87602082850101111561254557600080fd5b6020830194508093505050509250925092565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052601160045260246000fd5b6000821982111561259a5761259a612558565b500190565b600067ffffffffffffffff838116908316818110156125c0576125c0612558565b039392505050565b600067ffffffffffffffff8083168181036125e5576125e5612558565b6001019392505050565b60008282101561260157612601612558565b500390565b7f4e487b7100000000000000000000000000000000000000000000000000000000600052603260045260246000fd5b600082357fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff4183360301811261266957600080fd5b9190910192915050565b60008083357fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe18436030181126126a857600080fd5b83018035915067ffffffffffffffff8211156126c357600080fd5b6020019150368190038213156126d857600080fd5b9250929050565b60007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff820361271057612710612558565b5060010190565b73ffffffffffffffffffffffffffffffffffffffff8316815260006020604081840152835180604085015260005b8181101561276157858101830151858201606001528201612745565b81811115612773576000606083870101525b50601f017fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0169290920160600194935050505056fea164736f6c634300080f000a496e697469616c697a61626c653a20636f6e7472616374206973206e6f742069",
}

// ZKEVMABI is the input ABI used to generate the binding from.
// Deprecated: Use ZKEVMMetaData.ABI instead.
var ZKEVMABI = ZKEVMMetaData.ABI

// ZKEVMBin is the compiled bytecode used for deploying new contracts.
// Deprecated: Use ZKEVMMetaData.Bin instead.
var ZKEVMBin = ZKEVMMetaData.Bin

// DeployZKEVM deploys a new Ethereum contract, binding an instance of ZKEVM to it.
func DeployZKEVM(auth *bind.TransactOpts, backend bind.ContractBackend, _submitter common.Address, _challenger common.Address) (common.Address, *types.Transaction, *ZKEVM, error) {
	parsed, err := ZKEVMMetaData.GetAbi()
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	if parsed == nil {
		return common.Address{}, nil, nil, errors.New("GetABI returned nil")
	}

	address, tx, contract, err := bind.DeployContract(auth, *parsed, common.FromHex(ZKEVMBin), backend, _submitter, _challenger)
	if err != nil {
		return common.Address{}, nil, nil, err
	}
	return address, tx, &ZKEVM{ZKEVMCaller: ZKEVMCaller{contract: contract}, ZKEVMTransactor: ZKEVMTransactor{contract: contract}, ZKEVMFilterer: ZKEVMFilterer{contract: contract}}, nil
}

// ZKEVM is an auto generated Go binding around an Ethereum contract.
type ZKEVM struct {
	ZKEVMCaller     // Read-only binding to the contract
	ZKEVMTransactor // Write-only binding to the contract
	ZKEVMFilterer   // Log filterer for contract events
}

// ZKEVMCaller is an auto generated read-only Go binding around an Ethereum contract.
type ZKEVMCaller struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ZKEVMTransactor is an auto generated write-only Go binding around an Ethereum contract.
type ZKEVMTransactor struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ZKEVMFilterer is an auto generated log filtering Go binding around an Ethereum contract events.
type ZKEVMFilterer struct {
	contract *bind.BoundContract // Generic contract wrapper for the low level calls
}

// ZKEVMSession is an auto generated Go binding around an Ethereum contract,
// with pre-set call and transact options.
type ZKEVMSession struct {
	Contract     *ZKEVM            // Generic contract binding to set the session for
	CallOpts     bind.CallOpts     // Call options to use throughout this session
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// ZKEVMCallerSession is an auto generated read-only Go binding around an Ethereum contract,
// with pre-set call options.
type ZKEVMCallerSession struct {
	Contract *ZKEVMCaller  // Generic contract caller binding to set the session for
	CallOpts bind.CallOpts // Call options to use throughout this session
}

// ZKEVMTransactorSession is an auto generated write-only Go binding around an Ethereum contract,
// with pre-set transact options.
type ZKEVMTransactorSession struct {
	Contract     *ZKEVMTransactor  // Generic contract transactor binding to set the session for
	TransactOpts bind.TransactOpts // Transaction auth options to use throughout this session
}

// ZKEVMRaw is an auto generated low-level Go binding around an Ethereum contract.
type ZKEVMRaw struct {
	Contract *ZKEVM // Generic contract binding to access the raw methods on
}

// ZKEVMCallerRaw is an auto generated low-level read-only Go binding around an Ethereum contract.
type ZKEVMCallerRaw struct {
	Contract *ZKEVMCaller // Generic read-only contract binding to access the raw methods on
}

// ZKEVMTransactorRaw is an auto generated low-level write-only Go binding around an Ethereum contract.
type ZKEVMTransactorRaw struct {
	Contract *ZKEVMTransactor // Generic write-only contract binding to access the raw methods on
}

// NewZKEVM creates a new instance of ZKEVM, bound to a specific deployed contract.
func NewZKEVM(address common.Address, backend bind.ContractBackend) (*ZKEVM, error) {
	contract, err := bindZKEVM(address, backend, backend, backend)
	if err != nil {
		return nil, err
	}
	return &ZKEVM{ZKEVMCaller: ZKEVMCaller{contract: contract}, ZKEVMTransactor: ZKEVMTransactor{contract: contract}, ZKEVMFilterer: ZKEVMFilterer{contract: contract}}, nil
}

// NewZKEVMCaller creates a new read-only instance of ZKEVM, bound to a specific deployed contract.
func NewZKEVMCaller(address common.Address, caller bind.ContractCaller) (*ZKEVMCaller, error) {
	contract, err := bindZKEVM(address, caller, nil, nil)
	if err != nil {
		return nil, err
	}
	return &ZKEVMCaller{contract: contract}, nil
}

// NewZKEVMTransactor creates a new write-only instance of ZKEVM, bound to a specific deployed contract.
func NewZKEVMTransactor(address common.Address, transactor bind.ContractTransactor) (*ZKEVMTransactor, error) {
	contract, err := bindZKEVM(address, nil, transactor, nil)
	if err != nil {
		return nil, err
	}
	return &ZKEVMTransactor{contract: contract}, nil
}

// NewZKEVMFilterer creates a new log filterer instance of ZKEVM, bound to a specific deployed contract.
func NewZKEVMFilterer(address common.Address, filterer bind.ContractFilterer) (*ZKEVMFilterer, error) {
	contract, err := bindZKEVM(address, nil, nil, filterer)
	if err != nil {
		return nil, err
	}
	return &ZKEVMFilterer{contract: contract}, nil
}

// bindZKEVM binds a generic wrapper to an already deployed contract.
func bindZKEVM(address common.Address, caller bind.ContractCaller, transactor bind.ContractTransactor, filterer bind.ContractFilterer) (*bind.BoundContract, error) {
	parsed, err := ZKEVMMetaData.GetAbi()
	if err != nil {
		return nil, err
	}
	return bind.NewBoundContract(address, *parsed, caller, transactor, filterer), nil
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ZKEVM *ZKEVMRaw) Call(opts *bind.CallOpts, result *[]interface{}, method string, params ...interface{}) error {
	return _ZKEVM.Contract.ZKEVMCaller.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ZKEVM *ZKEVMRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ZKEVM.Contract.ZKEVMTransactor.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ZKEVM *ZKEVMRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ZKEVM.Contract.ZKEVMTransactor.contract.Transact(opts, method, params...)
}

// Call invokes the (constant) contract method with params as input values and
// sets the output to result. The result type might be a single field for simple
// returns, a slice of interfaces for anonymous returns and a struct for named
// returns.
func (_ZKEVM *ZKEVMCallerRaw) Call(opts *bind.CallOpts, result *[]interface{}, method string, params ...interface{}) error {
	return _ZKEVM.Contract.contract.Call(opts, result, method, params...)
}

// Transfer initiates a plain transaction to move funds to the contract, calling
// its default method if one is available.
func (_ZKEVM *ZKEVMTransactorRaw) Transfer(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ZKEVM.Contract.contract.Transfer(opts)
}

// Transact invokes the (paid) contract method with params as input values.
func (_ZKEVM *ZKEVMTransactorRaw) Transact(opts *bind.TransactOpts, method string, params ...interface{}) (*types.Transaction, error) {
	return _ZKEVM.Contract.contract.Transact(opts, method, params...)
}

// FINALIZATIONPERIODSECONDS is a free data retrieval call binding the contract method 0xf4daa291.
//
// Solidity: function FINALIZATION_PERIOD_SECONDS() view returns(uint256)
func (_ZKEVM *ZKEVMCaller) FINALIZATIONPERIODSECONDS(opts *bind.CallOpts) (*big.Int, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "FINALIZATION_PERIOD_SECONDS")

	if err != nil {
		return *new(*big.Int), err
	}

	out0 := *abi.ConvertType(out[0], new(*big.Int)).(**big.Int)

	return out0, err

}

// FINALIZATIONPERIODSECONDS is a free data retrieval call binding the contract method 0xf4daa291.
//
// Solidity: function FINALIZATION_PERIOD_SECONDS() view returns(uint256)
func (_ZKEVM *ZKEVMSession) FINALIZATIONPERIODSECONDS() (*big.Int, error) {
	return _ZKEVM.Contract.FINALIZATIONPERIODSECONDS(&_ZKEVM.CallOpts)
}

// FINALIZATIONPERIODSECONDS is a free data retrieval call binding the contract method 0xf4daa291.
//
// Solidity: function FINALIZATION_PERIOD_SECONDS() view returns(uint256)
func (_ZKEVM *ZKEVMCallerSession) FINALIZATIONPERIODSECONDS() (*big.Int, error) {
	return _ZKEVM.Contract.FINALIZATIONPERIODSECONDS(&_ZKEVM.CallOpts)
}

// MINDEPOSIT is a free data retrieval call binding the contract method 0xe1e158a5.
//
// Solidity: function MIN_DEPOSIT() view returns(uint256)
func (_ZKEVM *ZKEVMCaller) MINDEPOSIT(opts *bind.CallOpts) (*big.Int, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "MIN_DEPOSIT")

	if err != nil {
		return *new(*big.Int), err
	}

	out0 := *abi.ConvertType(out[0], new(*big.Int)).(**big.Int)

	return out0, err

}

// MINDEPOSIT is a free data retrieval call binding the contract method 0xe1e158a5.
//
// Solidity: function MIN_DEPOSIT() view returns(uint256)
func (_ZKEVM *ZKEVMSession) MINDEPOSIT() (*big.Int, error) {
	return _ZKEVM.Contract.MINDEPOSIT(&_ZKEVM.CallOpts)
}

// MINDEPOSIT is a free data retrieval call binding the contract method 0xe1e158a5.
//
// Solidity: function MIN_DEPOSIT() view returns(uint256)
func (_ZKEVM *ZKEVMCallerSession) MINDEPOSIT() (*big.Int, error) {
	return _ZKEVM.Contract.MINDEPOSIT(&_ZKEVM.CallOpts)
}

// PORTAL is a free data retrieval call binding the contract method 0x0ff754ea.
//
// Solidity: function PORTAL() view returns(address)
func (_ZKEVM *ZKEVMCaller) PORTAL(opts *bind.CallOpts) (common.Address, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "PORTAL")

	if err != nil {
		return *new(common.Address), err
	}

	out0 := *abi.ConvertType(out[0], new(common.Address)).(*common.Address)

	return out0, err

}

// PORTAL is a free data retrieval call binding the contract method 0x0ff754ea.
//
// Solidity: function PORTAL() view returns(address)
func (_ZKEVM *ZKEVMSession) PORTAL() (common.Address, error) {
	return _ZKEVM.Contract.PORTAL(&_ZKEVM.CallOpts)
}

// PORTAL is a free data retrieval call binding the contract method 0x0ff754ea.
//
// Solidity: function PORTAL() view returns(address)
func (_ZKEVM *ZKEVMCallerSession) PORTAL() (common.Address, error) {
	return _ZKEVM.Contract.PORTAL(&_ZKEVM.CallOpts)
}

// PROOFWINDOW is a free data retrieval call binding the contract method 0xeb1ec18f.
//
// Solidity: function PROOF_WINDOW() view returns(uint256)
func (_ZKEVM *ZKEVMCaller) PROOFWINDOW(opts *bind.CallOpts) (*big.Int, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "PROOF_WINDOW")

	if err != nil {
		return *new(*big.Int), err
	}

	out0 := *abi.ConvertType(out[0], new(*big.Int)).(**big.Int)

	return out0, err

}

// PROOFWINDOW is a free data retrieval call binding the contract method 0xeb1ec18f.
//
// Solidity: function PROOF_WINDOW() view returns(uint256)
func (_ZKEVM *ZKEVMSession) PROOFWINDOW() (*big.Int, error) {
	return _ZKEVM.Contract.PROOFWINDOW(&_ZKEVM.CallOpts)
}

// PROOFWINDOW is a free data retrieval call binding the contract method 0xeb1ec18f.
//
// Solidity: function PROOF_WINDOW() view returns(uint256)
func (_ZKEVM *ZKEVMCallerSession) PROOFWINDOW() (*big.Int, error) {
	return _ZKEVM.Contract.PROOFWINDOW(&_ZKEVM.CallOpts)
}

// Challenger is a free data retrieval call binding the contract method 0x534db0e2.
//
// Solidity: function challenger() view returns(address)
func (_ZKEVM *ZKEVMCaller) Challenger(opts *bind.CallOpts) (common.Address, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "challenger")

	if err != nil {
		return *new(common.Address), err
	}

	out0 := *abi.ConvertType(out[0], new(common.Address)).(*common.Address)

	return out0, err

}

// Challenger is a free data retrieval call binding the contract method 0x534db0e2.
//
// Solidity: function challenger() view returns(address)
func (_ZKEVM *ZKEVMSession) Challenger() (common.Address, error) {
	return _ZKEVM.Contract.Challenger(&_ZKEVM.CallOpts)
}

// Challenger is a free data retrieval call binding the contract method 0x534db0e2.
//
// Solidity: function challenger() view returns(address)
func (_ZKEVM *ZKEVMCallerSession) Challenger() (common.Address, error) {
	return _ZKEVM.Contract.Challenger(&_ZKEVM.CallOpts)
}

// Challenges is a free data retrieval call binding the contract method 0xc7ab2039.
//
// Solidity: function challenges(uint64 ) view returns(uint64 batchIndex, address challenger, uint256 challengeDeposit, uint256 startTime, bool finished)
func (_ZKEVM *ZKEVMCaller) Challenges(opts *bind.CallOpts, arg0 uint64) (struct {
	BatchIndex       uint64
	Challenger       common.Address
	ChallengeDeposit *big.Int
	StartTime        *big.Int
	Finished         bool
}, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "challenges", arg0)

	outstruct := new(struct {
		BatchIndex       uint64
		Challenger       common.Address
		ChallengeDeposit *big.Int
		StartTime        *big.Int
		Finished         bool
	})
	if err != nil {
		return *outstruct, err
	}

	outstruct.BatchIndex = *abi.ConvertType(out[0], new(uint64)).(*uint64)
	outstruct.Challenger = *abi.ConvertType(out[1], new(common.Address)).(*common.Address)
	outstruct.ChallengeDeposit = *abi.ConvertType(out[2], new(*big.Int)).(**big.Int)
	outstruct.StartTime = *abi.ConvertType(out[3], new(*big.Int)).(**big.Int)
	outstruct.Finished = *abi.ConvertType(out[4], new(bool)).(*bool)

	return *outstruct, err

}

// Challenges is a free data retrieval call binding the contract method 0xc7ab2039.
//
// Solidity: function challenges(uint64 ) view returns(uint64 batchIndex, address challenger, uint256 challengeDeposit, uint256 startTime, bool finished)
func (_ZKEVM *ZKEVMSession) Challenges(arg0 uint64) (struct {
	BatchIndex       uint64
	Challenger       common.Address
	ChallengeDeposit *big.Int
	StartTime        *big.Int
	Finished         bool
}, error) {
	return _ZKEVM.Contract.Challenges(&_ZKEVM.CallOpts, arg0)
}

// Challenges is a free data retrieval call binding the contract method 0xc7ab2039.
//
// Solidity: function challenges(uint64 ) view returns(uint64 batchIndex, address challenger, uint256 challengeDeposit, uint256 startTime, bool finished)
func (_ZKEVM *ZKEVMCallerSession) Challenges(arg0 uint64) (struct {
	BatchIndex       uint64
	Challenger       common.Address
	ChallengeDeposit *big.Int
	StartTime        *big.Int
	Finished         bool
}, error) {
	return _ZKEVM.Contract.Challenges(&_ZKEVM.CallOpts, arg0)
}

// ConfirmBatchIndex is a free data retrieval call binding the contract method 0xf71b51f3.
//
// Solidity: function confirmBatchIndex(uint64 ) view returns(bool)
func (_ZKEVM *ZKEVMCaller) ConfirmBatchIndex(opts *bind.CallOpts, arg0 uint64) (bool, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "confirmBatchIndex", arg0)

	if err != nil {
		return *new(bool), err
	}

	out0 := *abi.ConvertType(out[0], new(bool)).(*bool)

	return out0, err

}

// ConfirmBatchIndex is a free data retrieval call binding the contract method 0xf71b51f3.
//
// Solidity: function confirmBatchIndex(uint64 ) view returns(bool)
func (_ZKEVM *ZKEVMSession) ConfirmBatchIndex(arg0 uint64) (bool, error) {
	return _ZKEVM.Contract.ConfirmBatchIndex(&_ZKEVM.CallOpts, arg0)
}

// ConfirmBatchIndex is a free data retrieval call binding the contract method 0xf71b51f3.
//
// Solidity: function confirmBatchIndex(uint64 ) view returns(bool)
func (_ZKEVM *ZKEVMCallerSession) ConfirmBatchIndex(arg0 uint64) (bool, error) {
	return _ZKEVM.Contract.ConfirmBatchIndex(&_ZKEVM.CallOpts, arg0)
}

// Deposits is a free data retrieval call binding the contract method 0xfc7e286d.
//
// Solidity: function deposits(address ) view returns(uint256)
func (_ZKEVM *ZKEVMCaller) Deposits(opts *bind.CallOpts, arg0 common.Address) (*big.Int, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "deposits", arg0)

	if err != nil {
		return *new(*big.Int), err
	}

	out0 := *abi.ConvertType(out[0], new(*big.Int)).(**big.Int)

	return out0, err

}

// Deposits is a free data retrieval call binding the contract method 0xfc7e286d.
//
// Solidity: function deposits(address ) view returns(uint256)
func (_ZKEVM *ZKEVMSession) Deposits(arg0 common.Address) (*big.Int, error) {
	return _ZKEVM.Contract.Deposits(&_ZKEVM.CallOpts, arg0)
}

// Deposits is a free data retrieval call binding the contract method 0xfc7e286d.
//
// Solidity: function deposits(address ) view returns(uint256)
func (_ZKEVM *ZKEVMCallerSession) Deposits(arg0 common.Address) (*big.Int, error) {
	return _ZKEVM.Contract.Deposits(&_ZKEVM.CallOpts, arg0)
}

// IsBatchInChallenge is a free data retrieval call binding the contract method 0xacc1245a.
//
// Solidity: function isBatchInChallenge(uint64 batchIndex) view returns(bool)
func (_ZKEVM *ZKEVMCaller) IsBatchInChallenge(opts *bind.CallOpts, batchIndex uint64) (bool, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "isBatchInChallenge", batchIndex)

	if err != nil {
		return *new(bool), err
	}

	out0 := *abi.ConvertType(out[0], new(bool)).(*bool)

	return out0, err

}

// IsBatchInChallenge is a free data retrieval call binding the contract method 0xacc1245a.
//
// Solidity: function isBatchInChallenge(uint64 batchIndex) view returns(bool)
func (_ZKEVM *ZKEVMSession) IsBatchInChallenge(batchIndex uint64) (bool, error) {
	return _ZKEVM.Contract.IsBatchInChallenge(&_ZKEVM.CallOpts, batchIndex)
}

// IsBatchInChallenge is a free data retrieval call binding the contract method 0xacc1245a.
//
// Solidity: function isBatchInChallenge(uint64 batchIndex) view returns(bool)
func (_ZKEVM *ZKEVMCallerSession) IsBatchInChallenge(batchIndex uint64) (bool, error) {
	return _ZKEVM.Contract.IsBatchInChallenge(&_ZKEVM.CallOpts, batchIndex)
}

// IsStaked is a free data retrieval call binding the contract method 0x6177fd18.
//
// Solidity: function isStaked(address addr) view returns(bool)
func (_ZKEVM *ZKEVMCaller) IsStaked(opts *bind.CallOpts, addr common.Address) (bool, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "isStaked", addr)

	if err != nil {
		return *new(bool), err
	}

	out0 := *abi.ConvertType(out[0], new(bool)).(*bool)

	return out0, err

}

// IsStaked is a free data retrieval call binding the contract method 0x6177fd18.
//
// Solidity: function isStaked(address addr) view returns(bool)
func (_ZKEVM *ZKEVMSession) IsStaked(addr common.Address) (bool, error) {
	return _ZKEVM.Contract.IsStaked(&_ZKEVM.CallOpts, addr)
}

// IsStaked is a free data retrieval call binding the contract method 0x6177fd18.
//
// Solidity: function isStaked(address addr) view returns(bool)
func (_ZKEVM *ZKEVMCallerSession) IsStaked(addr common.Address) (bool, error) {
	return _ZKEVM.Contract.IsStaked(&_ZKEVM.CallOpts, addr)
}

// IsUserInChallenge is a free data retrieval call binding the contract method 0x23ec8518.
//
// Solidity: function isUserInChallenge(address user) view returns(bool)
func (_ZKEVM *ZKEVMCaller) IsUserInChallenge(opts *bind.CallOpts, user common.Address) (bool, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "isUserInChallenge", user)

	if err != nil {
		return *new(bool), err
	}

	out0 := *abi.ConvertType(out[0], new(bool)).(*bool)

	return out0, err

}

// IsUserInChallenge is a free data retrieval call binding the contract method 0x23ec8518.
//
// Solidity: function isUserInChallenge(address user) view returns(bool)
func (_ZKEVM *ZKEVMSession) IsUserInChallenge(user common.Address) (bool, error) {
	return _ZKEVM.Contract.IsUserInChallenge(&_ZKEVM.CallOpts, user)
}

// IsUserInChallenge is a free data retrieval call binding the contract method 0x23ec8518.
//
// Solidity: function isUserInChallenge(address user) view returns(bool)
func (_ZKEVM *ZKEVMCallerSession) IsUserInChallenge(user common.Address) (bool, error) {
	return _ZKEVM.Contract.IsUserInChallenge(&_ZKEVM.CallOpts, user)
}

// LastBatchSequenced is a free data retrieval call binding the contract method 0x423fa856.
//
// Solidity: function lastBatchSequenced() view returns(uint64)
func (_ZKEVM *ZKEVMCaller) LastBatchSequenced(opts *bind.CallOpts) (uint64, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "lastBatchSequenced")

	if err != nil {
		return *new(uint64), err
	}

	out0 := *abi.ConvertType(out[0], new(uint64)).(*uint64)

	return out0, err

}

// LastBatchSequenced is a free data retrieval call binding the contract method 0x423fa856.
//
// Solidity: function lastBatchSequenced() view returns(uint64)
func (_ZKEVM *ZKEVMSession) LastBatchSequenced() (uint64, error) {
	return _ZKEVM.Contract.LastBatchSequenced(&_ZKEVM.CallOpts)
}

// LastBatchSequenced is a free data retrieval call binding the contract method 0x423fa856.
//
// Solidity: function lastBatchSequenced() view returns(uint64)
func (_ZKEVM *ZKEVMCallerSession) LastBatchSequenced() (uint64, error) {
	return _ZKEVM.Contract.LastBatchSequenced(&_ZKEVM.CallOpts)
}

// LastL2BlockNumber is a free data retrieval call binding the contract method 0xf02deda1.
//
// Solidity: function lastL2BlockNumber() view returns(uint64)
func (_ZKEVM *ZKEVMCaller) LastL2BlockNumber(opts *bind.CallOpts) (uint64, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "lastL2BlockNumber")

	if err != nil {
		return *new(uint64), err
	}

	out0 := *abi.ConvertType(out[0], new(uint64)).(*uint64)

	return out0, err

}

// LastL2BlockNumber is a free data retrieval call binding the contract method 0xf02deda1.
//
// Solidity: function lastL2BlockNumber() view returns(uint64)
func (_ZKEVM *ZKEVMSession) LastL2BlockNumber() (uint64, error) {
	return _ZKEVM.Contract.LastL2BlockNumber(&_ZKEVM.CallOpts)
}

// LastL2BlockNumber is a free data retrieval call binding the contract method 0xf02deda1.
//
// Solidity: function lastL2BlockNumber() view returns(uint64)
func (_ZKEVM *ZKEVMCallerSession) LastL2BlockNumber() (uint64, error) {
	return _ZKEVM.Contract.LastL2BlockNumber(&_ZKEVM.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() view returns(address)
func (_ZKEVM *ZKEVMCaller) Owner(opts *bind.CallOpts) (common.Address, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "owner")

	if err != nil {
		return *new(common.Address), err
	}

	out0 := *abi.ConvertType(out[0], new(common.Address)).(*common.Address)

	return out0, err

}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() view returns(address)
func (_ZKEVM *ZKEVMSession) Owner() (common.Address, error) {
	return _ZKEVM.Contract.Owner(&_ZKEVM.CallOpts)
}

// Owner is a free data retrieval call binding the contract method 0x8da5cb5b.
//
// Solidity: function owner() view returns(address)
func (_ZKEVM *ZKEVMCallerSession) Owner() (common.Address, error) {
	return _ZKEVM.Contract.Owner(&_ZKEVM.CallOpts)
}

// StorageBatchs is a free data retrieval call binding the contract method 0xe291c2f5.
//
// Solidity: function storageBatchs(uint64 ) view returns(uint64 blockNumber, bytes32 withdrawRoot, bytes32 commitment, bytes32 stateRoot, uint256 originTimestamp)
func (_ZKEVM *ZKEVMCaller) StorageBatchs(opts *bind.CallOpts, arg0 uint64) (struct {
	BlockNumber     uint64
	WithdrawRoot    [32]byte
	Commitment      [32]byte
	StateRoot       [32]byte
	OriginTimestamp *big.Int
}, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "storageBatchs", arg0)

	outstruct := new(struct {
		BlockNumber     uint64
		WithdrawRoot    [32]byte
		Commitment      [32]byte
		StateRoot       [32]byte
		OriginTimestamp *big.Int
	})
	if err != nil {
		return *outstruct, err
	}

	outstruct.BlockNumber = *abi.ConvertType(out[0], new(uint64)).(*uint64)
	outstruct.WithdrawRoot = *abi.ConvertType(out[1], new([32]byte)).(*[32]byte)
	outstruct.Commitment = *abi.ConvertType(out[2], new([32]byte)).(*[32]byte)
	outstruct.StateRoot = *abi.ConvertType(out[3], new([32]byte)).(*[32]byte)
	outstruct.OriginTimestamp = *abi.ConvertType(out[4], new(*big.Int)).(**big.Int)

	return *outstruct, err

}

// StorageBatchs is a free data retrieval call binding the contract method 0xe291c2f5.
//
// Solidity: function storageBatchs(uint64 ) view returns(uint64 blockNumber, bytes32 withdrawRoot, bytes32 commitment, bytes32 stateRoot, uint256 originTimestamp)
func (_ZKEVM *ZKEVMSession) StorageBatchs(arg0 uint64) (struct {
	BlockNumber     uint64
	WithdrawRoot    [32]byte
	Commitment      [32]byte
	StateRoot       [32]byte
	OriginTimestamp *big.Int
}, error) {
	return _ZKEVM.Contract.StorageBatchs(&_ZKEVM.CallOpts, arg0)
}

// StorageBatchs is a free data retrieval call binding the contract method 0xe291c2f5.
//
// Solidity: function storageBatchs(uint64 ) view returns(uint64 blockNumber, bytes32 withdrawRoot, bytes32 commitment, bytes32 stateRoot, uint256 originTimestamp)
func (_ZKEVM *ZKEVMCallerSession) StorageBatchs(arg0 uint64) (struct {
	BlockNumber     uint64
	WithdrawRoot    [32]byte
	Commitment      [32]byte
	StateRoot       [32]byte
	OriginTimestamp *big.Int
}, error) {
	return _ZKEVM.Contract.StorageBatchs(&_ZKEVM.CallOpts, arg0)
}

// Submitter is a free data retrieval call binding the contract method 0x8dc45d9a.
//
// Solidity: function submitter() view returns(address)
func (_ZKEVM *ZKEVMCaller) Submitter(opts *bind.CallOpts) (common.Address, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "submitter")

	if err != nil {
		return *new(common.Address), err
	}

	out0 := *abi.ConvertType(out[0], new(common.Address)).(*common.Address)

	return out0, err

}

// Submitter is a free data retrieval call binding the contract method 0x8dc45d9a.
//
// Solidity: function submitter() view returns(address)
func (_ZKEVM *ZKEVMSession) Submitter() (common.Address, error) {
	return _ZKEVM.Contract.Submitter(&_ZKEVM.CallOpts)
}

// Submitter is a free data retrieval call binding the contract method 0x8dc45d9a.
//
// Solidity: function submitter() view returns(address)
func (_ZKEVM *ZKEVMCallerSession) Submitter() (common.Address, error) {
	return _ZKEVM.Contract.Submitter(&_ZKEVM.CallOpts)
}

// WithdrawRoots is a free data retrieval call binding the contract method 0x8ad9e18e.
//
// Solidity: function withdrawRoots(bytes32 ) view returns(uint256)
func (_ZKEVM *ZKEVMCaller) WithdrawRoots(opts *bind.CallOpts, arg0 [32]byte) (*big.Int, error) {
	var out []interface{}
	err := _ZKEVM.contract.Call(opts, &out, "withdrawRoots", arg0)

	if err != nil {
		return *new(*big.Int), err
	}

	out0 := *abi.ConvertType(out[0], new(*big.Int)).(**big.Int)

	return out0, err

}

// WithdrawRoots is a free data retrieval call binding the contract method 0x8ad9e18e.
//
// Solidity: function withdrawRoots(bytes32 ) view returns(uint256)
func (_ZKEVM *ZKEVMSession) WithdrawRoots(arg0 [32]byte) (*big.Int, error) {
	return _ZKEVM.Contract.WithdrawRoots(&_ZKEVM.CallOpts, arg0)
}

// WithdrawRoots is a free data retrieval call binding the contract method 0x8ad9e18e.
//
// Solidity: function withdrawRoots(bytes32 ) view returns(uint256)
func (_ZKEVM *ZKEVMCallerSession) WithdrawRoots(arg0 [32]byte) (*big.Int, error) {
	return _ZKEVM.Contract.WithdrawRoots(&_ZKEVM.CallOpts, arg0)
}

// ChallengeState is a paid mutator transaction binding the contract method 0x8d644bb7.
//
// Solidity: function challengeState(uint64 batchIndex) payable returns()
func (_ZKEVM *ZKEVMTransactor) ChallengeState(opts *bind.TransactOpts, batchIndex uint64) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "challengeState", batchIndex)
}

// ChallengeState is a paid mutator transaction binding the contract method 0x8d644bb7.
//
// Solidity: function challengeState(uint64 batchIndex) payable returns()
func (_ZKEVM *ZKEVMSession) ChallengeState(batchIndex uint64) (*types.Transaction, error) {
	return _ZKEVM.Contract.ChallengeState(&_ZKEVM.TransactOpts, batchIndex)
}

// ChallengeState is a paid mutator transaction binding the contract method 0x8d644bb7.
//
// Solidity: function challengeState(uint64 batchIndex) payable returns()
func (_ZKEVM *ZKEVMTransactorSession) ChallengeState(batchIndex uint64) (*types.Transaction, error) {
	return _ZKEVM.Contract.ChallengeState(&_ZKEVM.TransactOpts, batchIndex)
}

// ConfirmBatch is a paid mutator transaction binding the contract method 0x032ecb38.
//
// Solidity: function confirmBatch(uint64 batchIndex) returns()
func (_ZKEVM *ZKEVMTransactor) ConfirmBatch(opts *bind.TransactOpts, batchIndex uint64) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "confirmBatch", batchIndex)
}

// ConfirmBatch is a paid mutator transaction binding the contract method 0x032ecb38.
//
// Solidity: function confirmBatch(uint64 batchIndex) returns()
func (_ZKEVM *ZKEVMSession) ConfirmBatch(batchIndex uint64) (*types.Transaction, error) {
	return _ZKEVM.Contract.ConfirmBatch(&_ZKEVM.TransactOpts, batchIndex)
}

// ConfirmBatch is a paid mutator transaction binding the contract method 0x032ecb38.
//
// Solidity: function confirmBatch(uint64 batchIndex) returns()
func (_ZKEVM *ZKEVMTransactorSession) ConfirmBatch(batchIndex uint64) (*types.Transaction, error) {
	return _ZKEVM.Contract.ConfirmBatch(&_ZKEVM.TransactOpts, batchIndex)
}

// Initialize is a paid mutator transaction binding the contract method 0x485cc955.
//
// Solidity: function initialize(address _submitter, address _challenger) payable returns()
func (_ZKEVM *ZKEVMTransactor) Initialize(opts *bind.TransactOpts, _submitter common.Address, _challenger common.Address) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "initialize", _submitter, _challenger)
}

// Initialize is a paid mutator transaction binding the contract method 0x485cc955.
//
// Solidity: function initialize(address _submitter, address _challenger) payable returns()
func (_ZKEVM *ZKEVMSession) Initialize(_submitter common.Address, _challenger common.Address) (*types.Transaction, error) {
	return _ZKEVM.Contract.Initialize(&_ZKEVM.TransactOpts, _submitter, _challenger)
}

// Initialize is a paid mutator transaction binding the contract method 0x485cc955.
//
// Solidity: function initialize(address _submitter, address _challenger) payable returns()
func (_ZKEVM *ZKEVMTransactorSession) Initialize(_submitter common.Address, _challenger common.Address) (*types.Transaction, error) {
	return _ZKEVM.Contract.Initialize(&_ZKEVM.TransactOpts, _submitter, _challenger)
}

// ProveState is a paid mutator transaction binding the contract method 0x59ef1120.
//
// Solidity: function proveState(uint64 batchIndex, bytes proof) returns()
func (_ZKEVM *ZKEVMTransactor) ProveState(opts *bind.TransactOpts, batchIndex uint64, proof []byte) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "proveState", batchIndex, proof)
}

// ProveState is a paid mutator transaction binding the contract method 0x59ef1120.
//
// Solidity: function proveState(uint64 batchIndex, bytes proof) returns()
func (_ZKEVM *ZKEVMSession) ProveState(batchIndex uint64, proof []byte) (*types.Transaction, error) {
	return _ZKEVM.Contract.ProveState(&_ZKEVM.TransactOpts, batchIndex, proof)
}

// ProveState is a paid mutator transaction binding the contract method 0x59ef1120.
//
// Solidity: function proveState(uint64 batchIndex, bytes proof) returns()
func (_ZKEVM *ZKEVMTransactorSession) ProveState(batchIndex uint64, proof []byte) (*types.Transaction, error) {
	return _ZKEVM.Contract.ProveState(&_ZKEVM.TransactOpts, batchIndex, proof)
}

// RenounceOwnership is a paid mutator transaction binding the contract method 0x715018a6.
//
// Solidity: function renounceOwnership() returns()
func (_ZKEVM *ZKEVMTransactor) RenounceOwnership(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "renounceOwnership")
}

// RenounceOwnership is a paid mutator transaction binding the contract method 0x715018a6.
//
// Solidity: function renounceOwnership() returns()
func (_ZKEVM *ZKEVMSession) RenounceOwnership() (*types.Transaction, error) {
	return _ZKEVM.Contract.RenounceOwnership(&_ZKEVM.TransactOpts)
}

// RenounceOwnership is a paid mutator transaction binding the contract method 0x715018a6.
//
// Solidity: function renounceOwnership() returns()
func (_ZKEVM *ZKEVMTransactorSession) RenounceOwnership() (*types.Transaction, error) {
	return _ZKEVM.Contract.RenounceOwnership(&_ZKEVM.TransactOpts)
}

// SetPortal is a paid mutator transaction binding the contract method 0x4ff56192.
//
// Solidity: function setPortal(address _portal) returns()
func (_ZKEVM *ZKEVMTransactor) SetPortal(opts *bind.TransactOpts, _portal common.Address) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "setPortal", _portal)
}

// SetPortal is a paid mutator transaction binding the contract method 0x4ff56192.
//
// Solidity: function setPortal(address _portal) returns()
func (_ZKEVM *ZKEVMSession) SetPortal(_portal common.Address) (*types.Transaction, error) {
	return _ZKEVM.Contract.SetPortal(&_ZKEVM.TransactOpts, _portal)
}

// SetPortal is a paid mutator transaction binding the contract method 0x4ff56192.
//
// Solidity: function setPortal(address _portal) returns()
func (_ZKEVM *ZKEVMTransactorSession) SetPortal(_portal common.Address) (*types.Transaction, error) {
	return _ZKEVM.Contract.SetPortal(&_ZKEVM.TransactOpts, _portal)
}

// Stake is a paid mutator transaction binding the contract method 0x3a4b66f1.
//
// Solidity: function stake() payable returns()
func (_ZKEVM *ZKEVMTransactor) Stake(opts *bind.TransactOpts) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "stake")
}

// Stake is a paid mutator transaction binding the contract method 0x3a4b66f1.
//
// Solidity: function stake() payable returns()
func (_ZKEVM *ZKEVMSession) Stake() (*types.Transaction, error) {
	return _ZKEVM.Contract.Stake(&_ZKEVM.TransactOpts)
}

// Stake is a paid mutator transaction binding the contract method 0x3a4b66f1.
//
// Solidity: function stake() payable returns()
func (_ZKEVM *ZKEVMTransactorSession) Stake() (*types.Transaction, error) {
	return _ZKEVM.Contract.Stake(&_ZKEVM.TransactOpts)
}

// SubmitBatches is a paid mutator transaction binding the contract method 0x4b21f578.
//
// Solidity: function submitBatches((uint64,bytes,bytes,bytes32,bytes32,(bytes[],bytes))[] batches) returns()
func (_ZKEVM *ZKEVMTransactor) SubmitBatches(opts *bind.TransactOpts, batches []ZKEVMBatchData) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "submitBatches", batches)
}

// SubmitBatches is a paid mutator transaction binding the contract method 0x4b21f578.
//
// Solidity: function submitBatches((uint64,bytes,bytes,bytes32,bytes32,(bytes[],bytes))[] batches) returns()
func (_ZKEVM *ZKEVMSession) SubmitBatches(batches []ZKEVMBatchData) (*types.Transaction, error) {
	return _ZKEVM.Contract.SubmitBatches(&_ZKEVM.TransactOpts, batches)
}

// SubmitBatches is a paid mutator transaction binding the contract method 0x4b21f578.
//
// Solidity: function submitBatches((uint64,bytes,bytes,bytes32,bytes32,(bytes[],bytes))[] batches) returns()
func (_ZKEVM *ZKEVMTransactorSession) SubmitBatches(batches []ZKEVMBatchData) (*types.Transaction, error) {
	return _ZKEVM.Contract.SubmitBatches(&_ZKEVM.TransactOpts, batches)
}

// TransferOwnership is a paid mutator transaction binding the contract method 0xf2fde38b.
//
// Solidity: function transferOwnership(address newOwner) returns()
func (_ZKEVM *ZKEVMTransactor) TransferOwnership(opts *bind.TransactOpts, newOwner common.Address) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "transferOwnership", newOwner)
}

// TransferOwnership is a paid mutator transaction binding the contract method 0xf2fde38b.
//
// Solidity: function transferOwnership(address newOwner) returns()
func (_ZKEVM *ZKEVMSession) TransferOwnership(newOwner common.Address) (*types.Transaction, error) {
	return _ZKEVM.Contract.TransferOwnership(&_ZKEVM.TransactOpts, newOwner)
}

// TransferOwnership is a paid mutator transaction binding the contract method 0xf2fde38b.
//
// Solidity: function transferOwnership(address newOwner) returns()
func (_ZKEVM *ZKEVMTransactorSession) TransferOwnership(newOwner common.Address) (*types.Transaction, error) {
	return _ZKEVM.Contract.TransferOwnership(&_ZKEVM.TransactOpts, newOwner)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(uint256 amount) returns()
func (_ZKEVM *ZKEVMTransactor) Withdraw(opts *bind.TransactOpts, amount *big.Int) (*types.Transaction, error) {
	return _ZKEVM.contract.Transact(opts, "withdraw", amount)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(uint256 amount) returns()
func (_ZKEVM *ZKEVMSession) Withdraw(amount *big.Int) (*types.Transaction, error) {
	return _ZKEVM.Contract.Withdraw(&_ZKEVM.TransactOpts, amount)
}

// Withdraw is a paid mutator transaction binding the contract method 0x2e1a7d4d.
//
// Solidity: function withdraw(uint256 amount) returns()
func (_ZKEVM *ZKEVMTransactorSession) Withdraw(amount *big.Int) (*types.Transaction, error) {
	return _ZKEVM.Contract.Withdraw(&_ZKEVM.TransactOpts, amount)
}

// ZKEVMChallengeResIterator is returned from FilterChallengeRes and is used to iterate over the raw logs and unpacked data for ChallengeRes events raised by the ZKEVM contract.
type ZKEVMChallengeResIterator struct {
	Event *ZKEVMChallengeRes // Event containing the contract specifics and raw log

	contract *bind.BoundContract // Generic contract to use for unpacking event data
	event    string              // Event name to use for unpacking event data

	logs chan types.Log        // Log channel receiving the found contract events
	sub  ethereum.Subscription // Subscription for errors, completion and termination
	done bool                  // Whether the subscription completed delivering logs
	fail error                 // Occurred error to stop iteration
}

// Next advances the iterator to the subsequent event, returning whether there
// are any more events found. In case of a retrieval or parsing error, false is
// returned and Error() can be queried for the exact failure.
func (it *ZKEVMChallengeResIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(ZKEVMChallengeRes)
			if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
				it.fail = err
				return false
			}
			it.Event.Raw = log
			return true

		default:
			return false
		}
	}
	// Iterator still in progress, wait for either a data or an error event
	select {
	case log := <-it.logs:
		it.Event = new(ZKEVMChallengeRes)
		if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
			it.fail = err
			return false
		}
		it.Event.Raw = log
		return true

	case err := <-it.sub.Err():
		it.done = true
		it.fail = err
		return it.Next()
	}
}

// Error returns any retrieval or parsing error occurred during filtering.
func (it *ZKEVMChallengeResIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *ZKEVMChallengeResIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// ZKEVMChallengeRes represents a ChallengeRes event raised by the ZKEVM contract.
type ZKEVMChallengeRes struct {
	BatchIndex *big.Int
	Winner     common.Address
	Res        string
	Raw        types.Log // Blockchain specific contextual infos
}

// FilterChallengeRes is a free log retrieval operation binding the contract event 0xe70d3820e244d5f71d1a6395db24f3460e8dca966edc1fd3625b6292880a877a.
//
// Solidity: event ChallengeRes(uint256 indexed batchIndex, address winner, string res)
func (_ZKEVM *ZKEVMFilterer) FilterChallengeRes(opts *bind.FilterOpts, batchIndex []*big.Int) (*ZKEVMChallengeResIterator, error) {

	var batchIndexRule []interface{}
	for _, batchIndexItem := range batchIndex {
		batchIndexRule = append(batchIndexRule, batchIndexItem)
	}

	logs, sub, err := _ZKEVM.contract.FilterLogs(opts, "ChallengeRes", batchIndexRule)
	if err != nil {
		return nil, err
	}
	return &ZKEVMChallengeResIterator{contract: _ZKEVM.contract, event: "ChallengeRes", logs: logs, sub: sub}, nil
}

// WatchChallengeRes is a free log subscription operation binding the contract event 0xe70d3820e244d5f71d1a6395db24f3460e8dca966edc1fd3625b6292880a877a.
//
// Solidity: event ChallengeRes(uint256 indexed batchIndex, address winner, string res)
func (_ZKEVM *ZKEVMFilterer) WatchChallengeRes(opts *bind.WatchOpts, sink chan<- *ZKEVMChallengeRes, batchIndex []*big.Int) (event.Subscription, error) {

	var batchIndexRule []interface{}
	for _, batchIndexItem := range batchIndex {
		batchIndexRule = append(batchIndexRule, batchIndexItem)
	}

	logs, sub, err := _ZKEVM.contract.WatchLogs(opts, "ChallengeRes", batchIndexRule)
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(ZKEVMChallengeRes)
				if err := _ZKEVM.contract.UnpackLog(event, "ChallengeRes", log); err != nil {
					return err
				}
				event.Raw = log

				select {
				case sink <- event:
				case err := <-sub.Err():
					return err
				case <-quit:
					return nil
				}
			case err := <-sub.Err():
				return err
			case <-quit:
				return nil
			}
		}
	}), nil
}

// ParseChallengeRes is a log parse operation binding the contract event 0xe70d3820e244d5f71d1a6395db24f3460e8dca966edc1fd3625b6292880a877a.
//
// Solidity: event ChallengeRes(uint256 indexed batchIndex, address winner, string res)
func (_ZKEVM *ZKEVMFilterer) ParseChallengeRes(log types.Log) (*ZKEVMChallengeRes, error) {
	event := new(ZKEVMChallengeRes)
	if err := _ZKEVM.contract.UnpackLog(event, "ChallengeRes", log); err != nil {
		return nil, err
	}
	event.Raw = log
	return event, nil
}

// ZKEVMChallengeStateIterator is returned from FilterChallengeState and is used to iterate over the raw logs and unpacked data for ChallengeState events raised by the ZKEVM contract.
type ZKEVMChallengeStateIterator struct {
	Event *ZKEVMChallengeState // Event containing the contract specifics and raw log

	contract *bind.BoundContract // Generic contract to use for unpacking event data
	event    string              // Event name to use for unpacking event data

	logs chan types.Log        // Log channel receiving the found contract events
	sub  ethereum.Subscription // Subscription for errors, completion and termination
	done bool                  // Whether the subscription completed delivering logs
	fail error                 // Occurred error to stop iteration
}

// Next advances the iterator to the subsequent event, returning whether there
// are any more events found. In case of a retrieval or parsing error, false is
// returned and Error() can be queried for the exact failure.
func (it *ZKEVMChallengeStateIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(ZKEVMChallengeState)
			if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
				it.fail = err
				return false
			}
			it.Event.Raw = log
			return true

		default:
			return false
		}
	}
	// Iterator still in progress, wait for either a data or an error event
	select {
	case log := <-it.logs:
		it.Event = new(ZKEVMChallengeState)
		if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
			it.fail = err
			return false
		}
		it.Event.Raw = log
		return true

	case err := <-it.sub.Err():
		it.done = true
		it.fail = err
		return it.Next()
	}
}

// Error returns any retrieval or parsing error occurred during filtering.
func (it *ZKEVMChallengeStateIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *ZKEVMChallengeStateIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// ZKEVMChallengeState represents a ChallengeState event raised by the ZKEVM contract.
type ZKEVMChallengeState struct {
	BatchIndex       *big.Int
	Challenger       common.Address
	ChallengeDeposit *big.Int
	Raw              types.Log // Blockchain specific contextual infos
}

// FilterChallengeState is a free log retrieval operation binding the contract event 0xff4bd2fd14b0670e131544fdc1e7c53f06371ccac4a3a8e0445a93d02d68fb05.
//
// Solidity: event ChallengeState(uint256 indexed batchIndex, address challenger, uint256 challengeDeposit)
func (_ZKEVM *ZKEVMFilterer) FilterChallengeState(opts *bind.FilterOpts, batchIndex []*big.Int) (*ZKEVMChallengeStateIterator, error) {

	var batchIndexRule []interface{}
	for _, batchIndexItem := range batchIndex {
		batchIndexRule = append(batchIndexRule, batchIndexItem)
	}

	logs, sub, err := _ZKEVM.contract.FilterLogs(opts, "ChallengeState", batchIndexRule)
	if err != nil {
		return nil, err
	}
	return &ZKEVMChallengeStateIterator{contract: _ZKEVM.contract, event: "ChallengeState", logs: logs, sub: sub}, nil
}

// WatchChallengeState is a free log subscription operation binding the contract event 0xff4bd2fd14b0670e131544fdc1e7c53f06371ccac4a3a8e0445a93d02d68fb05.
//
// Solidity: event ChallengeState(uint256 indexed batchIndex, address challenger, uint256 challengeDeposit)
func (_ZKEVM *ZKEVMFilterer) WatchChallengeState(opts *bind.WatchOpts, sink chan<- *ZKEVMChallengeState, batchIndex []*big.Int) (event.Subscription, error) {

	var batchIndexRule []interface{}
	for _, batchIndexItem := range batchIndex {
		batchIndexRule = append(batchIndexRule, batchIndexItem)
	}

	logs, sub, err := _ZKEVM.contract.WatchLogs(opts, "ChallengeState", batchIndexRule)
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(ZKEVMChallengeState)
				if err := _ZKEVM.contract.UnpackLog(event, "ChallengeState", log); err != nil {
					return err
				}
				event.Raw = log

				select {
				case sink <- event:
				case err := <-sub.Err():
					return err
				case <-quit:
					return nil
				}
			case err := <-sub.Err():
				return err
			case <-quit:
				return nil
			}
		}
	}), nil
}

// ParseChallengeState is a log parse operation binding the contract event 0xff4bd2fd14b0670e131544fdc1e7c53f06371ccac4a3a8e0445a93d02d68fb05.
//
// Solidity: event ChallengeState(uint256 indexed batchIndex, address challenger, uint256 challengeDeposit)
func (_ZKEVM *ZKEVMFilterer) ParseChallengeState(log types.Log) (*ZKEVMChallengeState, error) {
	event := new(ZKEVMChallengeState)
	if err := _ZKEVM.contract.UnpackLog(event, "ChallengeState", log); err != nil {
		return nil, err
	}
	event.Raw = log
	return event, nil
}

// ZKEVMInitializedIterator is returned from FilterInitialized and is used to iterate over the raw logs and unpacked data for Initialized events raised by the ZKEVM contract.
type ZKEVMInitializedIterator struct {
	Event *ZKEVMInitialized // Event containing the contract specifics and raw log

	contract *bind.BoundContract // Generic contract to use for unpacking event data
	event    string              // Event name to use for unpacking event data

	logs chan types.Log        // Log channel receiving the found contract events
	sub  ethereum.Subscription // Subscription for errors, completion and termination
	done bool                  // Whether the subscription completed delivering logs
	fail error                 // Occurred error to stop iteration
}

// Next advances the iterator to the subsequent event, returning whether there
// are any more events found. In case of a retrieval or parsing error, false is
// returned and Error() can be queried for the exact failure.
func (it *ZKEVMInitializedIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(ZKEVMInitialized)
			if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
				it.fail = err
				return false
			}
			it.Event.Raw = log
			return true

		default:
			return false
		}
	}
	// Iterator still in progress, wait for either a data or an error event
	select {
	case log := <-it.logs:
		it.Event = new(ZKEVMInitialized)
		if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
			it.fail = err
			return false
		}
		it.Event.Raw = log
		return true

	case err := <-it.sub.Err():
		it.done = true
		it.fail = err
		return it.Next()
	}
}

// Error returns any retrieval or parsing error occurred during filtering.
func (it *ZKEVMInitializedIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *ZKEVMInitializedIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// ZKEVMInitialized represents a Initialized event raised by the ZKEVM contract.
type ZKEVMInitialized struct {
	Version uint8
	Raw     types.Log // Blockchain specific contextual infos
}

// FilterInitialized is a free log retrieval operation binding the contract event 0x7f26b83ff96e1f2b6a682f133852f6798a09c465da95921460cefb3847402498.
//
// Solidity: event Initialized(uint8 version)
func (_ZKEVM *ZKEVMFilterer) FilterInitialized(opts *bind.FilterOpts) (*ZKEVMInitializedIterator, error) {

	logs, sub, err := _ZKEVM.contract.FilterLogs(opts, "Initialized")
	if err != nil {
		return nil, err
	}
	return &ZKEVMInitializedIterator{contract: _ZKEVM.contract, event: "Initialized", logs: logs, sub: sub}, nil
}

// WatchInitialized is a free log subscription operation binding the contract event 0x7f26b83ff96e1f2b6a682f133852f6798a09c465da95921460cefb3847402498.
//
// Solidity: event Initialized(uint8 version)
func (_ZKEVM *ZKEVMFilterer) WatchInitialized(opts *bind.WatchOpts, sink chan<- *ZKEVMInitialized) (event.Subscription, error) {

	logs, sub, err := _ZKEVM.contract.WatchLogs(opts, "Initialized")
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(ZKEVMInitialized)
				if err := _ZKEVM.contract.UnpackLog(event, "Initialized", log); err != nil {
					return err
				}
				event.Raw = log

				select {
				case sink <- event:
				case err := <-sub.Err():
					return err
				case <-quit:
					return nil
				}
			case err := <-sub.Err():
				return err
			case <-quit:
				return nil
			}
		}
	}), nil
}

// ParseInitialized is a log parse operation binding the contract event 0x7f26b83ff96e1f2b6a682f133852f6798a09c465da95921460cefb3847402498.
//
// Solidity: event Initialized(uint8 version)
func (_ZKEVM *ZKEVMFilterer) ParseInitialized(log types.Log) (*ZKEVMInitialized, error) {
	event := new(ZKEVMInitialized)
	if err := _ZKEVM.contract.UnpackLog(event, "Initialized", log); err != nil {
		return nil, err
	}
	event.Raw = log
	return event, nil
}

// ZKEVMOwnershipTransferredIterator is returned from FilterOwnershipTransferred and is used to iterate over the raw logs and unpacked data for OwnershipTransferred events raised by the ZKEVM contract.
type ZKEVMOwnershipTransferredIterator struct {
	Event *ZKEVMOwnershipTransferred // Event containing the contract specifics and raw log

	contract *bind.BoundContract // Generic contract to use for unpacking event data
	event    string              // Event name to use for unpacking event data

	logs chan types.Log        // Log channel receiving the found contract events
	sub  ethereum.Subscription // Subscription for errors, completion and termination
	done bool                  // Whether the subscription completed delivering logs
	fail error                 // Occurred error to stop iteration
}

// Next advances the iterator to the subsequent event, returning whether there
// are any more events found. In case of a retrieval or parsing error, false is
// returned and Error() can be queried for the exact failure.
func (it *ZKEVMOwnershipTransferredIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(ZKEVMOwnershipTransferred)
			if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
				it.fail = err
				return false
			}
			it.Event.Raw = log
			return true

		default:
			return false
		}
	}
	// Iterator still in progress, wait for either a data or an error event
	select {
	case log := <-it.logs:
		it.Event = new(ZKEVMOwnershipTransferred)
		if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
			it.fail = err
			return false
		}
		it.Event.Raw = log
		return true

	case err := <-it.sub.Err():
		it.done = true
		it.fail = err
		return it.Next()
	}
}

// Error returns any retrieval or parsing error occurred during filtering.
func (it *ZKEVMOwnershipTransferredIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *ZKEVMOwnershipTransferredIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// ZKEVMOwnershipTransferred represents a OwnershipTransferred event raised by the ZKEVM contract.
type ZKEVMOwnershipTransferred struct {
	PreviousOwner common.Address
	NewOwner      common.Address
	Raw           types.Log // Blockchain specific contextual infos
}

// FilterOwnershipTransferred is a free log retrieval operation binding the contract event 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0.
//
// Solidity: event OwnershipTransferred(address indexed previousOwner, address indexed newOwner)
func (_ZKEVM *ZKEVMFilterer) FilterOwnershipTransferred(opts *bind.FilterOpts, previousOwner []common.Address, newOwner []common.Address) (*ZKEVMOwnershipTransferredIterator, error) {

	var previousOwnerRule []interface{}
	for _, previousOwnerItem := range previousOwner {
		previousOwnerRule = append(previousOwnerRule, previousOwnerItem)
	}
	var newOwnerRule []interface{}
	for _, newOwnerItem := range newOwner {
		newOwnerRule = append(newOwnerRule, newOwnerItem)
	}

	logs, sub, err := _ZKEVM.contract.FilterLogs(opts, "OwnershipTransferred", previousOwnerRule, newOwnerRule)
	if err != nil {
		return nil, err
	}
	return &ZKEVMOwnershipTransferredIterator{contract: _ZKEVM.contract, event: "OwnershipTransferred", logs: logs, sub: sub}, nil
}

// WatchOwnershipTransferred is a free log subscription operation binding the contract event 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0.
//
// Solidity: event OwnershipTransferred(address indexed previousOwner, address indexed newOwner)
func (_ZKEVM *ZKEVMFilterer) WatchOwnershipTransferred(opts *bind.WatchOpts, sink chan<- *ZKEVMOwnershipTransferred, previousOwner []common.Address, newOwner []common.Address) (event.Subscription, error) {

	var previousOwnerRule []interface{}
	for _, previousOwnerItem := range previousOwner {
		previousOwnerRule = append(previousOwnerRule, previousOwnerItem)
	}
	var newOwnerRule []interface{}
	for _, newOwnerItem := range newOwner {
		newOwnerRule = append(newOwnerRule, newOwnerItem)
	}

	logs, sub, err := _ZKEVM.contract.WatchLogs(opts, "OwnershipTransferred", previousOwnerRule, newOwnerRule)
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(ZKEVMOwnershipTransferred)
				if err := _ZKEVM.contract.UnpackLog(event, "OwnershipTransferred", log); err != nil {
					return err
				}
				event.Raw = log

				select {
				case sink <- event:
				case err := <-sub.Err():
					return err
				case <-quit:
					return nil
				}
			case err := <-sub.Err():
				return err
			case <-quit:
				return nil
			}
		}
	}), nil
}

// ParseOwnershipTransferred is a log parse operation binding the contract event 0x8be0079c531659141344cd1fd0a4f28419497f9722a3daafe3b4186f6b6457e0.
//
// Solidity: event OwnershipTransferred(address indexed previousOwner, address indexed newOwner)
func (_ZKEVM *ZKEVMFilterer) ParseOwnershipTransferred(log types.Log) (*ZKEVMOwnershipTransferred, error) {
	event := new(ZKEVMOwnershipTransferred)
	if err := _ZKEVM.contract.UnpackLog(event, "OwnershipTransferred", log); err != nil {
		return nil, err
	}
	event.Raw = log
	return event, nil
}

// ZKEVMSubmitBatchesIterator is returned from FilterSubmitBatches and is used to iterate over the raw logs and unpacked data for SubmitBatches events raised by the ZKEVM contract.
type ZKEVMSubmitBatchesIterator struct {
	Event *ZKEVMSubmitBatches // Event containing the contract specifics and raw log

	contract *bind.BoundContract // Generic contract to use for unpacking event data
	event    string              // Event name to use for unpacking event data

	logs chan types.Log        // Log channel receiving the found contract events
	sub  ethereum.Subscription // Subscription for errors, completion and termination
	done bool                  // Whether the subscription completed delivering logs
	fail error                 // Occurred error to stop iteration
}

// Next advances the iterator to the subsequent event, returning whether there
// are any more events found. In case of a retrieval or parsing error, false is
// returned and Error() can be queried for the exact failure.
func (it *ZKEVMSubmitBatchesIterator) Next() bool {
	// If the iterator failed, stop iterating
	if it.fail != nil {
		return false
	}
	// If the iterator completed, deliver directly whatever's available
	if it.done {
		select {
		case log := <-it.logs:
			it.Event = new(ZKEVMSubmitBatches)
			if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
				it.fail = err
				return false
			}
			it.Event.Raw = log
			return true

		default:
			return false
		}
	}
	// Iterator still in progress, wait for either a data or an error event
	select {
	case log := <-it.logs:
		it.Event = new(ZKEVMSubmitBatches)
		if err := it.contract.UnpackLog(it.Event, it.event, log); err != nil {
			it.fail = err
			return false
		}
		it.Event.Raw = log
		return true

	case err := <-it.sub.Err():
		it.done = true
		it.fail = err
		return it.Next()
	}
}

// Error returns any retrieval or parsing error occurred during filtering.
func (it *ZKEVMSubmitBatchesIterator) Error() error {
	return it.fail
}

// Close terminates the iteration process, releasing any pending underlying
// resources.
func (it *ZKEVMSubmitBatchesIterator) Close() error {
	it.sub.Unsubscribe()
	return nil
}

// ZKEVMSubmitBatches represents a SubmitBatches event raised by the ZKEVM contract.
type ZKEVMSubmitBatches struct {
	NumBatch uint64
	L2Num    uint64
	Raw      types.Log // Blockchain specific contextual infos
}

// FilterSubmitBatches is a free log retrieval operation binding the contract event 0xaff2dd67e4faff27d6d11dbdc2eda3379b944ad1b67b973265a60efd9cd08ac9.
//
// Solidity: event SubmitBatches(uint64 indexed numBatch, uint64 l2Num)
func (_ZKEVM *ZKEVMFilterer) FilterSubmitBatches(opts *bind.FilterOpts, numBatch []uint64) (*ZKEVMSubmitBatchesIterator, error) {

	var numBatchRule []interface{}
	for _, numBatchItem := range numBatch {
		numBatchRule = append(numBatchRule, numBatchItem)
	}

	logs, sub, err := _ZKEVM.contract.FilterLogs(opts, "SubmitBatches", numBatchRule)
	if err != nil {
		return nil, err
	}
	return &ZKEVMSubmitBatchesIterator{contract: _ZKEVM.contract, event: "SubmitBatches", logs: logs, sub: sub}, nil
}

// WatchSubmitBatches is a free log subscription operation binding the contract event 0xaff2dd67e4faff27d6d11dbdc2eda3379b944ad1b67b973265a60efd9cd08ac9.
//
// Solidity: event SubmitBatches(uint64 indexed numBatch, uint64 l2Num)
func (_ZKEVM *ZKEVMFilterer) WatchSubmitBatches(opts *bind.WatchOpts, sink chan<- *ZKEVMSubmitBatches, numBatch []uint64) (event.Subscription, error) {

	var numBatchRule []interface{}
	for _, numBatchItem := range numBatch {
		numBatchRule = append(numBatchRule, numBatchItem)
	}

	logs, sub, err := _ZKEVM.contract.WatchLogs(opts, "SubmitBatches", numBatchRule)
	if err != nil {
		return nil, err
	}
	return event.NewSubscription(func(quit <-chan struct{}) error {
		defer sub.Unsubscribe()
		for {
			select {
			case log := <-logs:
				// New log arrived, parse the event and forward to the user
				event := new(ZKEVMSubmitBatches)
				if err := _ZKEVM.contract.UnpackLog(event, "SubmitBatches", log); err != nil {
					return err
				}
				event.Raw = log

				select {
				case sink <- event:
				case err := <-sub.Err():
					return err
				case <-quit:
					return nil
				}
			case err := <-sub.Err():
				return err
			case <-quit:
				return nil
			}
		}
	}), nil
}

// ParseSubmitBatches is a log parse operation binding the contract event 0xaff2dd67e4faff27d6d11dbdc2eda3379b944ad1b67b973265a60efd9cd08ac9.
//
// Solidity: event SubmitBatches(uint64 indexed numBatch, uint64 l2Num)
func (_ZKEVM *ZKEVMFilterer) ParseSubmitBatches(log types.Log) (*ZKEVMSubmitBatches, error) {
	event := new(ZKEVMSubmitBatches)
	if err := _ZKEVM.contract.UnpackLog(event, "SubmitBatches", log); err != nil {
		return nil, err
	}
	event.Raw = log
	return event, nil
}
