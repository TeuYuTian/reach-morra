'reach 0.1';

const [ isResult, NO_WINS, A_WINS, B_WINS, DRAW,  ] = makeEnum(4);

// 0 = none, 1 = B wins, 2 = draw , 3 = A wins
const winner = (handAlfred, guessAlfred, handBrandon, guessBrandon) => {
  const total = handAlfred + handBrandon;

  if ( guessAlfred == total && guessBrandon == total  ) {
      // draw
      return DRAW
  }  else if ( guessBrandon == total) {
      // Brandon wins
      return B_WINS
  }
  else if ( guessAlfred == total ) { 
      // Alfred wins
      return A_WINS
  } else {
    // else no one wins
      return NO_WINS
  }
}
  
assert(winner(1,2,1,3 ) == A_WINS);
assert(winner(5,10,5,8 ) == A_WINS);
assert(winner(3,6,4,7 ) == B_WINS);
assert(winner(1,5,3,4 ) == B_WINS);

assert(winner(0,0,0,0 ) == DRAW);
assert(winner(2,4,2,4 ) == DRAW);
assert(winner(5,10,5,10 ) == DRAW);

assert(winner(3,6,2,4 ) == NO_WINS);
assert(winner(0,3,1,5 ) == NO_WINS);

forall(UInt, handAlfred =>
  forall(UInt, handBrandon =>
    forall(UInt, guessAlfred =>
      forall(UInt, guessBrandon =>
    assert(isResult(winner(handAlfred, guessAlfred, handBrandon , guessBrandon)))
))));

//common functions
const commonInteract = {
  ...hasRandom,
  reportResult: Fun([UInt], Null),
  reportHands: Fun([UInt, UInt, UInt, UInt], Null),
  informTimeout: Fun([], Null),
  getHand: Fun([], UInt),
  getGuess: Fun([], UInt),
};

const alfredInterect = {
  ...commonInteract,
  wager: UInt, 
  deadline: UInt, 
}

const brandonInteract = {
  ...commonInteract,
  acceptWager: Fun([UInt], Null),
}


export const main = Reach.App(() => {
  const Alfred = Participant('Alfred',alfredInterect );
  const Brandon = Participant('Brandon', brandonInteract );
  init();

  // Check for timeouts
  const informTimeout = () => {
    each([Alfred, Brandon], () => {
      interact.informTimeout();
    });
  };

  Alfred.only(() => {
    const wager = declassify(interact.wager);
    const deadline = declassify(interact.deadline);
  });
  Alfred.publish(wager, deadline)
    .pay(wager);
  commit();

  Brandon.only(() => {
    interact.acceptWager(wager);
  });
  Brandon.pay(wager)
    .timeout(relativeTime(deadline), () => closeTo(Alfred, informTimeout));
  

  var result = DRAW;
   invariant( balance() == 2 * wager && isResult(result) );

  //////////// When DRAW or NO_WINS ///////////////////
   while ( result == DRAW || result == NO_WINS ) {
    commit();

  Alfred.only(() => {
    const _handAlfred = interact.getHand();
    const [_commitAlfred1, _saltAlfred1] = makeCommitment(interact, _handAlfred);
    const commitAlfred1 = declassify(_commitAlfred1);

    const _guessAlfred = interact.getGuess();
    const [_commitAlfred2, _saltAlfred2] = makeCommitment(interact, _guessAlfred);
    const commitAlfred2 = declassify(_commitAlfred2);

  })
  

  Alfred.publish(commitAlfred1, commitAlfred2)
      .timeout(relativeTime(deadline), () => closeTo(Brandon, informTimeout));
    commit();

  // Brandon must NOT know about Alfred hand and guess
  unknowable(Brandon, Alfred(_handAlfred,_guessAlfred, _saltAlfred1,_saltAlfred2 ));
  
  // Get Brandon hand
  Brandon.only(() => {
    const handBrandon = declassify(interact.getHand());
    const guessBrandon = declassify(interact.getGuess());
  });

  Brandon.publish(handBrandon, guessBrandon)
    .timeout(relativeTime(deadline), () => closeTo(Alfred, informTimeout));
  commit();

  Alfred.only(() => {
    const saltAlfred1 = declassify(_saltAlfred1);
    const handAlfred = declassify(_handAlfred);
    const saltAlfred2 = declassify(_saltAlfred2);
    const guessAlfred = declassify(_guessAlfred);
  });

  Alfred.publish(saltAlfred1,saltAlfred2, handAlfred, guessAlfred)
  .timeout(relativeTime(deadline), () => closeTo(Brandon, informTimeout));
  checkCommitment(commitAlfred1, saltAlfred1, handAlfred);
  checkCommitment(commitAlfred2, saltAlfred2, guessAlfred);

  // Report results to all participants
  each([Alfred, Brandon], () => {
    interact.reportHands(handAlfred, guessAlfred, handBrandon, guessBrandon);
  });

  result = winner(handAlfred, guessAlfred, handBrandon, guessBrandon);
  continue;
}
// ensure no DRAW or NO_WINS
assert(result == A_WINS || result == B_WINS);

each([Alfred, Brandon], () => {
  interact.reportResult(result);
});

transfer(2 * wager).to(result == A_WINS ? Alfred : Brandon);
commit();
});
