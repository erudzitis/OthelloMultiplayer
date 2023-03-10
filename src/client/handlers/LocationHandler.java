package client.handlers;

import client.exceptions.GameNotFoundException;
import client.operators.SysoutOperator;
import game.OthelloGame;

import java.util.Queue;

/**
 * Runnable that applies incoming validated moves from the server
 * (stored in the queue) to the ongoing game instance,
 * and performs post-update processing, to coordinate the ComputerPlayers turn (if assigned),
 * and handle the case scenario when client has no possible moves left.
 */
public class LocationHandler implements Runnable {
    /**
     * Reference back to the GameHandler instance that holds the queue.
     */
    private final GameHandler gameHandler;

    /**
     * Constructor
     * @param gameHandler GameHandler assigned to the ongoing game.
     */
    /*@requires gameHandler != null; @*/
    public LocationHandler(GameHandler gameHandler) {
        this.gameHandler = gameHandler;
    }

    /**
     * Internal 'helper' method that applies all queued locations
     * @param locationQueue Queue<Integer>
     */
    /*@requires locationQueue.equals(gameHandler.getQueue()); @*/
    private void applyLocations(Queue<Integer> locationQueue) {
        if (!this.gameHandler.hasOngoingGame()) {
            return;
        }

        // If there are un-applied moves that we should keep track of, we apply them,
        // all the move locations must be valid out of the box, because they came from the server
        for (int i = 0; i < locationQueue.size(); i++) {
            int location = locationQueue.remove();
            System.out.println("Received location " + location);
            this.gameHandler.getGame().doMove(this.gameHandler.getGame().locationToMove(location));
            this.gameHandler.getClient().getMessageOperator().incomingMessage(
                this.gameHandler.getGame().getBoard().toString());

            if (location == OthelloGame.PASSING_MOVE_INDEX) {
                this.gameHandler.getClient().getMessageOperator().incomingMessage(
                    SysoutOperator.INFO + " A game turn was skipped!");
            }
        }

    }

    /**
     * Internal post update method that automatically skips current clients turn
     * if no moves are available
     */
    /*@ensures gameHandler.isComputerPlaying() && gameHandler.isClientsTurn()
        ==> gameHandler.isComputerPlayerTurn() == true; */
    private void postUpdate() {
        if (!this.gameHandler.hasOngoingGame()) {
            return;
        }

        // If an AI is running, it will automatically skip if no moves are valid.
        // However, we need to keep track of ComputerPlayers turn
        if (this.gameHandler.isComputerPlaying()) {
            // Check if clients move went through, in case it was performed by the AI
            if (this.gameHandler.isClientsTurn()) {
                // If so, we notify the AIHandler running that it should determine the next move
                synchronized (this.gameHandler.getComputerPlayer()) {
                    this.gameHandler.setComputerPlayerTurn(true);
                    this.gameHandler.getComputerPlayer().notify();
                }
            }

            return;
        }

        // Check if client can even make any more moves
        if (this.gameHandler.isClientsTurn()
                && this.gameHandler.getGame().getValidMoves(
                    this.gameHandler.getGame().getPlayerTurn()).isEmpty()) {
            // No moves are available for client in current turn, skipping turn
            try {
                this.gameHandler.skipTurn();
            } catch (GameNotFoundException ignored) {
                // LocationHandler thread only will be running if there is ongoing game
            }
        }
    }

    /**
     * Runs this operation
     */
    /*@requires gameHandler.hasOngoingGame(); @*/
    @Override
    public void run() {
        while (this.gameHandler.hasOngoingGame()) {
            synchronized (this.gameHandler.getQueue()) {
                // Game location queue reference
                Queue<Integer> locationQueue = this.gameHandler.getQueue();

                while (locationQueue.isEmpty()) {
                    try {
                        locationQueue.wait();
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                }

                this.applyLocations(locationQueue);
                this.postUpdate();
            }
        }
    }
}

