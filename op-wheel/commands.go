package wheel

import (
	"context"
	"encoding"
	"encoding/json"
	"fmt"
	"io"
	"math/big"
	"os"
	"strings"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/rpc"
	"github.com/urfave/cli"

	"github.com/ethereum-optimism/optimism/op-node/client"
	opservice "github.com/ethereum-optimism/optimism/op-service"
	oplog "github.com/ethereum-optimism/optimism/op-service/log"
	opmetrics "github.com/ethereum-optimism/optimism/op-service/metrics"
	"github.com/ethereum-optimism/optimism/op-wheel/cheat"
	"github.com/ethereum-optimism/optimism/op-wheel/engine"
)

const envVarPrefix = "OP_WHEEL"

var (
	DataDirFlag = cli.StringFlag{
		Name:     "data-dir",
		Usage:    "Geth data dir location.",
		Required: true,
		EnvVar:   opservice.PrefixEnvVar(envVarPrefix, "DATA_DIR"),
	}
	EngineEndpoint = cli.StringFlag{
		Name: "engine",
		Usage: "Engine API RPC endpoint, can be HTTP/WS/IPC",
		Required: true,
		EnvVar: opservice.PrefixEnvVar(envVarPrefix, "ENGINE"),
	}
	EngineJWTPath = cli.StringFlag{
		Name: "engine.jwt-secret",
		Usage: "Path to JWT secret file used to authenticate Engine API communication with.",
		Required: true,
		EnvVar: opservice.PrefixEnvVar(envVarPrefix, "ENGINE_JWT_SECRET"),
	}
	FeeRecipientFlag = cli.GenericFlag{
		Name:      "fee-recipient",
		Usage:     "fee-recipient of the block building",
		EnvVar:    opservice.PrefixEnvVar(envVarPrefix, "FEE_RECIPIENT"),
		Value:     &TextFlag[*common.Address]{Value: &common.Address{1: 0x13, 2: 0x37}},
	}
	RandaoFlag = cli.GenericFlag{
		Name:      "randao",
		Usage:     "randao value of the block building",
		EnvVar:    opservice.PrefixEnvVar(envVarPrefix, "RANDAO"),
		Value:     &TextFlag[*common.Hash]{Value: &common.Hash{1: 0x13, 2: 0x37}},
	}
	BlockTimeFlag = cli.Uint64Flag{
		Name:        "block-time",
		Usage:       "block time, interval of timestamps between blocks to build, in seconds",
		EnvVar:      opservice.PrefixEnvVar(envVarPrefix, "BLOCK_TIME"),
		Value:       12,
	}
	BuildingTime = cli.DurationFlag{
		Name:        "building-time",
		Usage:       "duration of of block building, this should be set to something lower than the block time.",
		EnvVar:      opservice.PrefixEnvVar(envVarPrefix, "BUILDING_TIME"),
		Value:       time.Second * 6,
	}
)

func ParseBuildingArgs(ctx *cli.Context) *engine.BlockBuildingSettings {
	return &engine.BlockBuildingSettings{
		BlockTime:    ctx.Uint64(BlockTimeFlag.Name),
		Random:       hashFlagValue(RandaoFlag.Name, ctx),
		FeeRecipient: addrFlagValue(FeeRecipientFlag.Name, ctx),
		BuildTime:    ctx.Duration(BuildingTime.Name),
	}
}

func CheatAction(readOnly bool, fn func(ctx *cli.Context, ch *cheat.Cheater) error) cli.ActionFunc {
	return func(ctx *cli.Context) error {
		dataDir := ctx.String(DataDirFlag.Name)
		ch, err := cheat.OpenGethDB(dataDir, readOnly)
		if err != nil {
			return fmt.Errorf("failed to open geth db: %w", err)
		}
		return fn(ctx, ch)
	}
}

func EngineAction(fn func(ctx *cli.Context, client client.RPC) error) cli.ActionFunc {
	return func(ctx *cli.Context) error {
		jwtData, err := os.ReadFile(ctx.String(EngineJWTPath.Name))
		if err != nil {
			return fmt.Errorf("failed to read jwt: %w", err)
		}
		secret := common.HexToHash(strings.TrimSpace(string(jwtData)))
		endpoint := ctx.String(EngineEndpoint.Name)
		client, err := engine.DialClient(context.Background(), endpoint, secret)
		if err != nil {
			return fmt.Errorf("failed to dial Engine API endpoint %q: %w", endpoint, err)
		}
		return fn(ctx, client)
	}
}

type Text interface {
	encoding.TextUnmarshaler
	fmt.Stringer
}

type TextFlag[T Text] struct {
	Value T
}

func (a *TextFlag[T]) Set(value string) error {
	return a.Value.UnmarshalText([]byte(value))
}

func (a *TextFlag[T]) String() string {
	return a.Value.String()
}

func (a *TextFlag[T]) Get() T {
	return a.Value
}

var _ cli.Generic = (*TextFlag[*common.Address])(nil)

func textFlag[T Text](name string, usage string) cli.GenericFlag {
	return cli.GenericFlag{
		Name:      name,
		Usage:     usage,
		EnvVar:    opservice.PrefixEnvVar(envVarPrefix, strings.ToUpper(name)),
		Required:  true,
		Value:     new(TextFlag[T]),
	}
}

func addrFlag(name string, usage string) cli.GenericFlag {
	return textFlag[*common.Address](name, usage)
}

func hashFlag(name string, usage string) cli.GenericFlag {
	return textFlag[*common.Hash](name, usage)
}

func bigFlag(name string, usage string) cli.GenericFlag {
	return textFlag[*big.Int](name, usage)
}

func addrFlagValue(name string, ctx *cli.Context) common.Address {
	return *ctx.Generic(name).(*TextFlag[*common.Address]).Value
}

func hashFlagValue(name string, ctx *cli.Context) common.Hash {
	return *ctx.Generic(name).(*TextFlag[*common.Hash]).Value
}

func bigFlagValue(name string, ctx *cli.Context) *big.Int {
	return ctx.Generic(name).(*TextFlag[*big.Int]).Value
}

var (
	CheatStorageGetCmd = cli.Command{
		Name:    "get",
		Aliases: []string{"read"},
		Flags: []cli.Flag{
			DataDirFlag,
			addrFlag("address", "Address to read storage of"),
			hashFlag("key", "key in storage of address to read value"),
		},
		Action: CheatAction(true, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.StorageGet(addrFlagValue("address", ctx), hashFlagValue("key", ctx), ctx.App.Writer))
		}),
	}
	CheatStorageSetCmd = cli.Command{
		Name:    "set",
		Aliases: []string{"write"},
		Flags: []cli.Flag{
			DataDirFlag,
			addrFlag("address", "Address to write storage of"),
			hashFlag("key", "key in storage of address to set value of"),
			hashFlag("value", "the value to write"),
		},
		Action: CheatAction(false, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.StorageSet(addrFlagValue("address", ctx), hashFlagValue("key", ctx), hashFlagValue("value", ctx)))
		}),
	}
	CheatStorageReadAll = cli.Command{
		Name:    "read-all",
		Aliases: []string{"get-all"},
		Usage: "Read all storage of the given account",
		Flags: []cli.Flag{DataDirFlag, addrFlag("address", "Address to read all storage of")},
		Action: CheatAction(true, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.StorageReadAll(addrFlagValue("address", ctx), ctx.App.Writer))
		}),
	}
	CheatStorageDiffCmd = cli.Command{
		Name: "diff",
		Usage: "Diff the storage of accounts A and B",
		Flags: []cli.Flag{DataDirFlag, hashFlag("a", "address of account A"), hashFlag("b", "address of account B")},
		Action: CheatAction(true, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.StorageDiff(ctx.App.Writer, addrFlagValue("a", ctx), addrFlagValue("b", ctx)))
		}),
	}
	CheatStoragePatchCmd = cli.Command{
		Name: "patch",
		Usage: "Apply storage patch from STDIN to the given account address",
		Flags: []cli.Flag{DataDirFlag, addrFlag("address", "Address to patch storage of")},
		Action: CheatAction(false, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.StoragePatch(os.Stdin, addrFlagValue("address", ctx)))
		}),
	}
	CheatStorageCmd = cli.Command{
		Name: "storage",
		Subcommands: []cli.Command{
			CheatStorageGetCmd,
			CheatStorageSetCmd,
			CheatStorageReadAll,
			CheatStorageDiffCmd,
			CheatStoragePatchCmd,
		},
	}
	CheatSetBalanceCmd = cli.Command{
		Name: "balance",
		Flags: []cli.Flag{
			DataDirFlag,
			addrFlag("address", "Address to change balance of"),
			bigFlag("balance", "New balance of the account"),
		},
		Action: CheatAction(false, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.SetBalance(addrFlagValue("address", ctx), bigFlagValue("balance", ctx)))
		}),
	}
	CheatSetNonceCmd = cli.Command{
		Name: "nonce",
		Flags: []cli.Flag{
			DataDirFlag,
			addrFlag("address", "Address to change nonce of"),
			bigFlag("nonce", "New nonce of the account"),
		},
		Action: CheatAction(false, func(ctx *cli.Context, ch *cheat.Cheater) error {
			return ch.RunAndClose(cheat.SetNonce(addrFlagValue("address", ctx), bigFlagValue("balance", ctx).Uint64()))
		}),
	}
	CheatOvmOwnersCmd = cli.Command{
		Name: "ovm-owners",
		Flags: []cli.Flag{
			DataDirFlag,
			cli.StringFlag{
				Name: "config",
				Usage: "Path to JSON config of OVM address replacements to apply.",
				Required: true,
				EnvVar: opservice.PrefixEnvVar(envVarPrefix, "OVM_OWNERS"),
				Value: "ovm-owners.json",
			},
		},
		Action: CheatAction(false, func(ctx *cli.Context, ch *cheat.Cheater) error {
			confData, err := os.ReadFile(ctx.String("config"))
			if err != nil {
				return fmt.Errorf("failed to read OVM owners JSON config file: %w", err)
			}
			var conf cheat.OvmOwnersConfig
			if err := json.Unmarshal(confData, &conf); err != nil {
				return err
			}
			return ch.RunAndClose(cheat.OvmOwners(&conf))
		}),
	}
	EngineBlockCmd = cli.Command{
		Name: "block",
		Usage: "build the next block using the Engine API",
		Flags: []cli.Flag{
			EngineEndpoint, EngineJWTPath,
			FeeRecipientFlag, RandaoFlag, BlockTimeFlag, BuildingTime,
		},
		// TODO: maybe support transaction and tx pool engine flags, since we use op-geth?
		// TODO: reorg flag
		// TODO: finalize/safe flag

		Action: EngineAction(func(ctx *cli.Context, client client.RPC) error {
			settings := ParseBuildingArgs(ctx)
			status, err := engine.Status(context.Background(), client)
			if err != nil {
				return err
			}
			payload, err := engine.BuildBlock(context.Background(), client, status, settings)
			if err != nil {
				return err
			}
			_, err = io.WriteString(ctx.App.Writer, payload.BlockHash.String())
			return err
		}),
	}
	EngineAutoCmd = cli.Command{
		Name: "auto",
		Usage: "Run a proof-of-nothing chain with fixed block time.",
		Description: "The block time can be changed. The execution engine must be synced to a post-Merge state first.",
		Flags: []cli.Flag{
			EngineEndpoint, EngineJWTPath,
			FeeRecipientFlag, RandaoFlag, BlockTimeFlag, BuildingTime,
		},
		Action: EngineAction(func(ctx *cli.Context, client client.RPC) error {
			logCfg := oplog.ReadCLIConfig(ctx)
			if err := logCfg.Check(); err != nil {
				return fmt.Errorf("failed to parse log configuration: %w", err)
			}
			l := oplog.NewLogger(logCfg)

			settings := ParseBuildingArgs(ctx)
			// TODO: finalize/safe flag

			metricsCfg := opmetrics.ReadCLIConfig(ctx)

			return opservice.CloseAction(func(ctx context.Context, shutdown <-chan struct{}) error {
				registry := opmetrics.NewRegistry()
				metrics := engine.NewMetrics("wheel", registry)
				if metricsCfg.Enabled {
					l.Info("starting metrics server", "addr", metricsCfg.ListenAddr, "port", metricsCfg.ListenPort)
					go func() {
						if err := opmetrics.ListenAndServe(ctx, registry, metricsCfg.ListenAddr, metricsCfg.ListenPort); err != nil {
							l.Error("error starting metrics server", err)
						}
					}()
				}
				return engine.Auto(ctx, metrics, client, l, shutdown, settings)
			})
		}),
	}
	EngineStatusCmd = cli.Command{
		Name: "status",
		Flags: []cli.Flag{EngineEndpoint, EngineJWTPath},
		Action: EngineAction(func(ctx *cli.Context, client client.RPC) error {
			stat, err := engine.Status(context.Background(), client)
			if err != nil {
				return err
			}
			enc := json.NewEncoder(ctx.App.Writer)
			enc.SetIndent("", "  ")
			return enc.Encode(stat)
		}),
	}
	EngineCopyCmd = cli.Command{
		Name: "copy",
		Flags: []cli.Flag{
			EngineEndpoint, EngineJWTPath,
			cli.StringFlag{
				Name: "source",
				Usage: "Unauthenticated regular eth JSON RPC to pull block data from, can be HTTP/WS/IPC.",
				Required: true,
				EnvVar: opservice.PrefixEnvVar(envVarPrefix, "ENGINE"),
			},
		},
		Action: EngineAction(func(ctx *cli.Context, dest client.RPC) error {
			rpcClient, err := rpc.DialOptions(context.Background(), ctx.String("source"))
			if err != nil {
				return fmt.Errorf("failed to dial engine source endpoint: %w", err)
			}
			source := client.NewBaseRPCClient(rpcClient)
			return engine.Copy(context.Background(), source, dest)
		}),
	}
)

var CheatCmd = cli.Command{
	Name:  "cheat",
	Usage: "Cheating commands to modify a Geth database.",
	Description: "Each sub-command opens a Geth database, applies the cheat, and then saves and closes the database." +
		"The Geth node will live in its own false reality, other nodes cannot sync the cheated state if they process the blocks.",
	Subcommands: []cli.Command{
		CheatStorageCmd,
		CheatSetBalanceCmd,
		CheatSetNonceCmd,
		CheatOvmOwnersCmd,
	},
}

var EngineCmd = cli.Command{
	Name:        "engine",
	Usage:       "Engine API commands to build/reorg/finalize blocks.",
	Description: "Each sub-command dials the engine API endpoint (with provided JWT secret) and then runs the action",
	Subcommands: []cli.Command{
		EngineBlockCmd,
		EngineAutoCmd,
		EngineStatusCmd,
		EngineCopyCmd,
	},
}
