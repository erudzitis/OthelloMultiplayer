package server;

import game.BoardGame;
import game.board.BoardMove;
import game.players.Player;
import networking.Protocol;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.util.List;
import java.util.Optional;

/**
 * Runnable that handles assigned games state on the server
 * by receiving forwarded messages from either one of ClientHandlers (2 client participants for each game),
 * validating them, updating state and finally performing server related room object clean up
 */
public class GameHandler implements Runnable {
    /**
     * Holds the reference of the server
     */
    private final Server server;

    /**
     * Hold the reference back to the GameRoom that initialized this GameHandler, needed for clean up purposes
     */
    private final GameRoom gameRoom;

    /**
     * Holds the reference to the particular board game
     */
    private final BoardGame game;

    /**
     * Reader for incoming protocol move sequences
     */
    Reader input;

    /**
     * Indicates whether room clean up is performed after the game has ended
     */
    private boolean isCleanupPerformed = false;

    /**
     * Initializes server and game reference
     *
     * @param server Server reference
     * @param gameRoom GameRoom reference that initialized the GameHandler
     * @param game   BoardGame, handler for that specific game instance
     * @param input  Reader piped input for GameHandler to use
     */
    public GameHandler(Server server, GameRoom gameRoom, BoardGame game, Reader input) {
        this.server = server;
        this.gameRoom = gameRoom;
        this.game = game;
        this.input = input;
    }

    /**
     * Returns the game instance that is assigned to this game handler
     *
     * @return BoardGame instance
     */
    public BoardGame getGame() {
        return this.game;
    }

    /**
     * Indicates whether the GameHandler object has completed its cleanup process,
     * clean up process will only be initializes if the game is over or directly requested
     * by the client handler
     *
     * @return boolean
     */
    public boolean isCleanupPerformed() {
        return this.isCleanupPerformed;
    }

    /**
     * Internal method that performs room clean up after the end of the game
     * @param clientUsernames List<String> client usernames in a game
     */
    private void performCleanup(List<String> clientUsernames) {
        this.server.cleanUpGameRoom(clientUsernames);

        // Update the state, indicating that clean up was finished
        this.isCleanupPerformed = true;

        // Notifying the client handler waiting on this game room,
        // ClientHandler will be waiting on the GameRoom, for cleanup to finish,
        // after forwarding this inner protocol message to this GameHandler
        synchronized (this.gameRoom) {
            this.gameRoom.notifyAll();
        }
    }

    /**
     * Internal method that checks the game state, being the game over, it informs all clients and performs cleanup
     * @param clientUsernames List<String> client usernames in a game
     */
    private void checkGameOver(List<String> clientUsernames) {
        // Check if the performed move lead to game over
        if (this.game.isGameOver()) {
            // Getting the winner
            Player winner = this.game.getWinner();

            // If there's no winner, it's a draw
            if (winner == null) {
                this.server.broadCastMessage(Protocol.gameOverFormat(Protocol.DRAW, null), clientUsernames);
            } else {
                // Otherwise, we inform winner and looser separately
                this.server.broadCastMessage(Protocol.gameOverFormat(Protocol.VICTORY, winner.getUsername()),
                        clientUsernames);
            }

            // Perform cleanup
            this.performCleanup(clientUsernames);
        }
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        // Reading the move protocol sequences piped to this game handler
        try (BufferedReader bf = new BufferedReader(this.input)) {
            // Reading line by line
            String line;

            while ((line = bf.readLine()) != null) {
                handleIncomingCommand(line);
            }
        } catch (IOException e) {
            // Cleaning up the room
            this.performCleanup(this.game.getPlayers().stream().map(Player::getUsername).toList());
        }
    }

    /**
     * Internal method that handles all incoming commands from the client
     *
     * @param line String line that we received from the server
     */
    /*@requires line != null; @*/
    private void handleIncomingCommand(String line) {
        String command = Protocol.commandExtract(line);

        switch (command) {
            case Protocol.MOVE -> {
                // Retrieving the desired move location of the client
                int desiredLocation = Protocol.moveExtract(line);

                // If the move is not valid, we must forward a message back to the original client,
                // indicating that the move is not valid
                BoardMove clientMove = this.game.locationToMove(desiredLocation);

                // Move is not valid, sending ERROR protocol message back to the client through client handler
                if (clientMove == null) {
                    this.server.getClientHandlersReverse().get(
                            this.game.getPlayerTurn().getUsername()).sendMessage(Protocol.errorFormat());
                    break;
                }

                List<String> clientUsernames = this.game.getPlayers().stream().map(Player::getUsername).toList();

                // Otherwise, keeping track of the move on the server
                this.game.doMove(clientMove);

                // And broadcasting the move to all other clients in the game room
                this.server.broadCastMessage(Protocol.moveFormat(desiredLocation), clientUsernames);

                // Check game state
                this.checkGameOver(clientUsernames);
            }
            case Protocol.DISCONNECT -> {
                // Extracting the name of one of the players that disconnected
                String disconnectedUsername = Protocol.clientDisconnectedExtract(line);

                // Getting the player that still remains in the game
                Optional<Player> remainingPlayer = this.game.getPlayers().stream()
                        .filter(player -> !player.getUsername().equals(disconnectedUsername)).findFirst();

                // Sending game over sequence to the remaining player that is going to become the winner automatically
                remainingPlayer.ifPresent(player ->
                    this.server.broadCastMessage(Protocol.gameOverFormat(Protocol.DISCONNECT, null), player.getUsername())
                );

                // Cleaning up the room
                this.performCleanup(this.game.getPlayers().stream().map(Player::getUsername).toList());
            }
        }
    }
}
