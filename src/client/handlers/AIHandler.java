package client.handlers;

import game.board.BoardMove;

public class AIHandler implements Runnable {
    /**
     * Reference back to the GameHandler instance that holds the queue
     */
    private final GameHandler gameHandler;

    public AIHandler(GameHandler gameHandler) {
        this.gameHandler = gameHandler;
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        while (this.gameHandler.hasOngoingGame()) {
            synchronized (this.gameHandler.getComputerPlayer()) {
                // If it's not clients turn or no AI is assigned, we put the thread to 'sleep' and wait for being notified
                while (!this.gameHandler.isComputerPlayerTurn()) {
                    try {
                        this.gameHandler.getComputerPlayer().wait();
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                }

                // It's clients turn, determine the move
                BoardMove move = this.gameHandler.getComputerPlayer().determineMove(this.gameHandler.getGame());

                // Submit it to the server
                this.gameHandler.getClient().attemptMove(move.getLocation());

                // Update the state
                this.gameHandler.setComputerPlayerTurn(false);
            }
        }
    }
}
