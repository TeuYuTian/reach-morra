<template>
  <div id="app">

  <H1>MORRA GAME</H1>

    <H3>Choose your role:</H3>
    <b-button variant="primary" @click="alfred()" >Alfred</b-button> VS 
    <b-button variant="primary" @click="brandon()" >Brandon</b-button>
    <BR/>
  
  <HR/>

  <div v-if="role==0">
  <h3>Alfred</h3>

    <b-button variant="secondary" @click="createContract()" >Click to Deploy Contract</b-button><BR/>

    contract: (Copy below to other participant)<BR/> 
    <h4>{{ ctcInfoStr }}</h4><BR /><BR />
  </div>

  <div v-else-if="role==1">
  <h3>Brandon</h3>

  <input v-model="ctcStr" placeholder="paste contract here"> <b-button variant="secondary" @click="attachContract()">Attach Contract</b-button>
  
    <BR/>  
    <div v-if="wager>0">
      Do you want to accept wager of {{wager}} ? 
      <BR/>
      <b-button variant="success" class="mx-2" @click="yesnoWager(true)">YES</b-button>
      <b-button variant="danger" @click="yesnoWager(false)" >NO</b-button>
    </div>
    <BR/>     
  </div>

  <HR/>

    <div v-if="displayHandsState">
      <BR/>
      <h4>Last result are : </h4>
      <BR/>
      Alfred hand: {{alfredHands}}
      Alfred guess: {{alfredGuess}}
      <BR/>
      Brandon hand: {{brandonHands}}
      Brandon guess: {{brandonGuess}}
      <BR/>
  </div>

  <div v-if="getHandState">
      Play your hand : <BR/>
      <b-button variant="secondary" class="mx-2" @click="readHand(0)">ZERO</b-button>
      <b-button variant="secondary" class="mx-2" @click="readHand(1)">ONE</b-button>
      <b-button variant="secondary" class="mx-2" @click="readHand(2)">TWO</b-button> 
      <b-button variant="secondary" class="mx-2" @click="readHand(3)">THREE</b-button> 
      <b-button variant="secondary" class="mx-2" @click="readHand(4)">FOUR</b-button> 
      <b-button variant="secondary" class="mx-2" @click="readHand(5)">FIVE</b-button> 
      <BR/>
  </div>

  <div v-if="getGuessState">
      Shout your total : <BR/>
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(0)"> 0 </b-button>
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(1)"> 1 </b-button>
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(2)"> 2 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(3)"> 3 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1"  @click="readGuess(4)"> 4 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(5)"> 5 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(6)"> 6 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(7)"> 7 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(8)"> 8 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(9)"> 9 </b-button> 
      <b-button variant="secondary" class="mx-2 my-1" @click="readGuess(10)"> 10 </b-button> 
      <BR/>
    </div>   

  <div v-if="displayResultState">
      <H3>{{resultString}}</H3>
  </div>
  
  <BR/>

  <HR/>
  addr: {{ addr}} <BR/>
  bal: {{ bal }} <BR/>
  balAtomic: {{ balAtomic }}<BR/>

  <b-button variant="secondary" @click="updateBalance()">updateBalance</b-button>

  </div>
</template>

<script>
import * as backend from '../build/index.main.mjs';
import { loadStdlib } from '@reach-sh/stdlib';
//const stdlib = loadStdlib(process.env);

// Run in cmdline with 
// REACH_CONNECTOR_MODE=ALGO-Live
// ../reach devnet
const stdlib = loadStdlib("ALGO");
stdlib.setProviderByName("TestNet")

console.log(`The consensus network is ${stdlib.connector}.`);

//const suStr = stdlib.standardUnit;
//console.log("Unit is ", suStr)
//const toAU = (su) => stdlib.parseCurrency(su);
const toSU = (au) => stdlib.formatCurrency(au, 4);

// Defined all interact methods as global for backend calls, 
// later convert them to Vue methods
// These object MUST match the contract object in index.rsh

// This MUST match object in index.rsh
let commonInteract = { };
let alfredInteract = { };
let brandonInteract = { };

const OUTCOME = [ "NULL","Alfred Wins", "Brandon Wins" ];

// Setup secret seed here, loaded in .env.local
const secret = process.env.VUE_APP_SECRET1
const secret2 = process.env.VUE_APP_SECRET2

export default {
  name: 'App',
  components: {
  },
  data: () => {
    return {
      role: 0,
      acc: undefined,
      addr: undefined,
      balAtomic: undefined,
      bal: undefined,
      faucetLoading: false,
      ctc: undefined,
      ctcInfoStr: undefined,
      ctcStr: undefined,

      contractCreated: false,
      displayResultState: false,
      displayHandsState: false,
      getGuessState: false,
      getHandState: false,

      wager: undefined,
      hand: undefined,
      guess: undefined,
      alfredHands:undefined,
      alfredGuess:undefined,
      brandonHands:undefined,
      brandonGuess:undefined,
      resultString: undefined,
      acceptWager: undefined,
    };
  },
   methods: {

      // Create a Vue methods for every commonInteract methods
      commonFunctions() {

        commonInteract = {
            ...stdlib.hasRandom,
            reportResult: async (result) => { this.reportResult(result); },
            reportHands: (alfred, alfredGuess, brandon, brandonGuess) => { this.reportHands(alfred, alfredGuess, brandon, brandonGuess)},
            informTimeout: () => { this.informTimeout()},
            getHand: async () => {
                  console.log("*** getHand called from backend");
                  // this will use v-if to display the input
                  this.getHandState = true
                  // waitUtil hand is not undefined
                  await this.waitUntil(() => this.hand !== undefined );
                  console.log("You played ", this.hand + " finger(s)");
                  const hand = stdlib.parseCurrency(this.hand);
                  this.hand = undefined;
                  this.getHandState = false
                  return hand;
                },
            getGuess: async () => {
                  console.log("*** getGuess called from backend");
                  // this will use v-if to display the input
                  this.getGuessState = true
                  // waitUtil hand is not undefined
                  await this.waitUntil(() => this.guess !== undefined );
                  console.log("You guess total of ", this.guess);
                  const guess = stdlib.parseCurrency(this.guess);
                  this.guess = undefined;
                  this.getGuessState = false
                  return guess;
                },
          }
      },

      async reportResult(result) {
        // Return is 0x01 - Alfred or 0x02 - Brandon
        // How to convert to number ??
        console.log('*** reportResult ', result);
        this.resultString = OUTCOME[result];
        console.log('this.result ', this.resultString);
        // change state to true and display to web
        this.displayResultState = true;
        await this.updateBalance();
      },

      reportHands(alfred, alfredGuess, brandon, brandonGuess) {
        console.log('*** The hands are ' + alfred, alfredGuess, brandon, brandonGuess );
        this.alfredHands = toSU(alfred);
        this.alfredGuess = toSU(alfredGuess);
        this.brandonHands = toSU(brandon);
        this.brandonGuess = toSU(brandonGuess);

        // change state to true and display to web
        this.displayHandsState = true;
      },

      readHand(hand) {
        console.log("readHand: ", hand)
        this.hand = hand;
      },

      readGuess(guess) {
        console.log("readguess: ", guess)
        this.guess = guess;
      },

    async createContract() {
          // create the contract here
          // https://docs.reach.sh/frontend/#ref-frontends-js-ctc
          console.log("Creating contract...")
          this.ctc = await this.acc.contract(backend);

          // The object must match backend in index.rsh
          this.ctc.p.Alfred(alfredInteract);

          // This will be ran after the contract is deployed
          // the JSON contract will be displayed so others can attach this contract
          const info = await this.ctc.getInfo();
          this.ctcInfoStr = JSON.stringify(info);
          console.log("this.ctcInfoStr: ", this.ctcInfoStr);

          this.contractCreated = true;
          await this.updateBalance();
    },

    async alfred() {
      this.commonFunctions();
      alfredInteract = {
            ...commonInteract,
            wager: stdlib.parseCurrency(1),
            deadline: stdlib.parseCurrency(10),
        }

      console.log("Alfred: ", alfredInteract);
      try {
          this.role = 0;
           // Change from devnet to testnet
          //this.acc = await stdlib.newTestAccount(stdlib.parseCurrency(1000));
          // Get secret keywords from .env.local
          this.acc = await stdlib.newAccountFromMnemonic(secret);

          this.addr = stdlib.formatAddress(this.acc.getAddress());

          this.balAtomic = await stdlib.balanceOf(this.acc);
          this.bal = String(stdlib.formatCurrency(this.balAtomic, 4));
            
      } catch (err) {
        console.log(err);
      }
    },
    
    //////////////////////////// Brandon

    async yesnoWager(res) {
        console.log("yesnoWager: ", res)
        this.acceptWager = res;
    },

   async attachContract() {
            this.ctc = await this.acc.contract(backend, JSON.parse(this.ctcStr));     
            console.log("Contract attached: ",this.ctcStr)
            await this.ctc.p.Brandon(brandonInteract);
            await this.updateBalance();
    },

    async brandon() {
      this.commonFunctions();
      brandonInteract = {
        ...commonInteract,
         //acceptWager: Fun([UInt], Null),
          acceptWager: async (wager) => {
          console.log("*** acceptWager", wager);

          this.wager =  toSU(wager),
          this.waitUntil( ()=> this.acceptWager == true)
          // Exit if false
          if ( this.acceptWager == false) {
              process.exit(0);
          }
        }
      }
      console.log("Brandon: ", brandonInteract);

      try {
        // Set role, create account
          this.role = 1;
          // Change from devnet to testnet
          //this.acc = await stdlib.newTestAccount(stdlib.parseCurrency(1000));
          // Get secret keywords from .env.local
          this.acc = await stdlib.newAccountFromMnemonic(secret2);

          this.addr = stdlib.formatAddress(this.acc.getAddress());

          this.balAtomic = await stdlib.balanceOf(this.acc);
          this.bal = String(stdlib.formatCurrency(this.balAtomic, 4));

      } catch (err) {
        console.log(err);
      }
    },  
    
    // Common function for all Vue Rech
    waitUntil (condition) {
    return new Promise((resolve) => {
        let interval = setInterval(() => {
            if (!condition()) {
                return
            }

            clearInterval(interval)
            resolve()
        }, 100)
      })
    },

    // Call this after every action to get current balance
    async updateBalance() {
      try {
        this.balAtomic = await stdlib.balanceOf(this.acc);
        this.bal = String(stdlib.formatCurrency(this.balAtomic, 4));
      } catch (err) {
        console.log(err);
      }
    },
  },
  computed: {
  },
  mounted() {
  }
}
</script>

<style>
#app {
  /* font-family: Avenir, Helvetica, Arial, sans-serif; */
  font-family: DM sans, sans-serif;
  -webkit-font-smoothing: antialiased;
  -moz-osx-font-smoothing: grayscale;
  text-align: center;
  color: #2c3e50;
  margin-top: 60px;
}
#wizard {
  width: 1024px;
}


.content {
  width: 1024px;
}
.navigation-buttons {
  display: flex;
  justify-content: space-between;
}
</style>
