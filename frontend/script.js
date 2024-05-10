function toHome() {
    window.location.href = '/home.html'
}

function toFormalModel() {
    window.location.href = '/formalmodel.html'
}

function toVerification() {
    window.location.href = '/verification.html'
}

function toPaper() {
    window.location.href = '/paper.html'
}


function updateCodeBlock() {
    const codeSelector = document.getElementById('code-block-selector');
    const codeBox = document.getElementById('code-box');
    const titleBox = document.getElementById('title-box');
    const selectedValue = codeSelector.value;

    switch (selectedValue) {
        case 'transactions':
            codeBox.innerHTML = transactions_def;
            titleBox.innerHTML = 'Transactions';
            break;
        case 'mining':
            codeBox.innerHTML = mining_def;
            titleBox.innerHTML = 'Mining';
            break;
        case 'contract':
            codeBox.innerHTML = reg_contract_def;
            titleBox.innerHTML = 'Register Contract';
            break;
        case 'blocks':
            codeBox.innerHTML = blocks_def;
            titleBox.innerHTML = 'Blocks';
            break;
        case 'channel':
            codeBox.innerHTML = channel_def;
            titleBox.innerHTML = 'Channel';
            break;
        case 'blockchain':
            codeBox.innerHTML = blockchain_def;
            titleBox.innerHTML = 'Integrated Blockchain System';
            break;
        case 'hacked':
            codeBox.innerHTML = hacked_def;
            titleBox.innerHTML = 'Hacked';
            break;
        default:
          codeBox.innerHTML = transactions_def;
          titleBox.innerHTML = 'Transactions';
    }
}

const transactions_def = `
                    Definition TRANSACTIONS_def:
                        TRANSACTIONS pending_tx mine =
                            ∀t. (case pending_tx t of
                                   []      => (mine t = NO_DATA) /\\ (pending_tx (t+1) = [])
                                 | (x::xs) => (mine t = DATA x) /\\ (pending_tx (t+1) = xs))
                    End
`;

const mining_def = `
                    Definition MINING_def:
                        MINING mine sc_tx = ∀t. (sc_tx t = mine t)
                    End
`;

const reg_contract_def = `
                    Definition REGISTER_CONTRACT_def:
                        REGISTER_CONTRACT sc_tx block_tx reg success =
                            ∀t. (case (sc_tx t) of
                                    DATA x =>
                                        (if (FIND_USER(x, (reg t)))
                                            then
                                             ((block_tx t = DATA x) /\\ (reg (t+1) = reg t) /\\ (success t = F))
                                        else
                                            ((block_tx t = DATA x) /\\ (reg (t+1) = x::(reg t)) /\\
                                            (success t = T)))
                                 | NO_DATA => ((block_tx t = NO_DATA) /\\ (reg (t+1) = reg t) /\\
                                                (success t = T)))
                    End
`;

const blocks_def = `
                    Definition BLOCKS_def:
                        BLOCKS block_tx blocks =
                            ∀t. (case block_tx t of
                                   DATA x  => (blocks (t+1) = (x::(blocks t)))
                                 | NO_DATA => (blocks (t+1) = (blocks t)))
                    End
`;

const channel_def = `
                    Definition CHANNEL_def:
                        CHANNEL tc dtc input output =
                            ∀t. if t < tc then
                                    output t = NO_DATA
                                else
                                    output t = input (t - dtc t) \/\ 0 < tc /\\ (dtc t = tc)
                    End
`;

const blockchain_def = `
                    Definition BLOCKCHAIN_def:
                        BLOCKCHAIN tc1 dtc1 tc2 dtc2 tc3 dtc3 ch1 ch2 ch3 pending_tx mine sc_tx
                                 reg success block_tx blocks =
                            ((TRANSACTIONS pending_tx ch1) /\\
                            (CHANNEL tc1 dtc1 ch1 mine) /\\
                            (MINING mine ch2) /\\
                            (CHANNEL tc2 dtc2 ch2 sc_tx) /\\
                            (REGISTER_CONTRACT sc_tx ch3 reg success) /\\
                            (CHANNEL tc3 dtc3 ch3 block_tx) /\\
                            (BLOCKS block_tx blocks))
                    End
`;

const hacked_def = `
                    Definition HACKED_PENDING_TX_def:
                        HACKED_PENDING_TX tc pending_tx
                            = ∃t. (t < tc) /\\ ~(pending_tx t = [])
                    End
`;