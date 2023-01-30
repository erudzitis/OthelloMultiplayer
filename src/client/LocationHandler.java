package client;

import client.exceptions.GameNotFoundException;
import game.OthelloGame;

import java.util.Queue;

/**
 * Runnable that applies incoming validated moves from the server to the ongoing game instance
 */
public class LocationHandler implements Runnable {
    /**
     * Reference back to the GameHandler instance that holds the queue
     */
    private final GameHandler gameHandler;

    public LocationHandler(GameHandler gameHandler) {
        this.gameHandler = gameHandler;
    }

    /**
     * Internal method that applies all queued locations
     * @param locationQueue Queue<Integer>
     */
    private void applyLocations(Queue<Integer> locationQueue) {
        // If there are un-applied moves that we should keep track of, we apply them,
        // all the move locations must be valid out of the box, because they came from the server
        for (int i = 0; i < locationQueue.size(); i++) {
            int location = locationQueue.remove();
            this.gameHandler.getGame().doMove(this.gameHandler.getGame().locationToMove(location));
            this.gameHandler.getClient().getMessageHandler().incomingMessage(this.gameHandler.getGame().getBoard().toString());

            if (location == OthelloGame.PASSING_MOVE_INDEX) {
                this.gameHandler.getClient().getMessageHandler().incomingMessage("\uD83D\uDCA1 A game turn was skipped!");
            }
        }

    }

    /**
     * Internal post update method that automatically skips current clients turn if no moves are available
     */
    private void postUpdate() {
        // Check if client can even make any more moves
        if (this.gameHandler.getClient().getUsername().equals(this.gameHandler.getGame().getPlayerTurn().getUsername())
                && this.gameHandler.getGame().getValidMoves(this.gameHandler.getGame().getPlayerTurn()).isEmpty()) {
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

