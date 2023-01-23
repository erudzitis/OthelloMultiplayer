package server;

import game.BoardGame;
import game.board.BoardMove;
import game.players.Player;
import networking.Protocol;

import java.io.BufferedReader;
import java.io.IOException;
import java.io.Reader;
import java.io.Writer;
import java.util.List;
import java.util.Optional;
import java.util.stream.Collectors;

/**
 * Runnable that handles assigned games state
 */
public class GameHandler implements Runnable {
    /**
     * Holds the reference of the server
     */
    private Server server;

    /**
     * Holds the reference to the particular board game
     */
    private BoardGame game;

    /**
     * Reader for incoming protocol move sequences
     */
    Reader input;

    /**
     * Initializes server and game reference
     *
     * @param server Server
     * @param game   BoardGame, handler for that specific game instance
     * @param input  Reader
     */
    public GameHandler(Server server, BoardGame game, Reader input) {
        this.server = server;
        this.game = game;
        this.input = input;
    }

    public BoardGame getGame() {
        return this.game;
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
            // TODO: Read on how to properly handle this exception
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
            case Protocol.MOVE:
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

                // Otherwise, keeping track of the move on the server
                this.game.doMove(clientMove);

                // And broadcasting the move to all other clients in the game room
                this.server.broadCastMessage(Protocol.moveFormat(desiredLocation),
                        this.game.getPlayers().stream().map(player -> player.getUsername()).collect(Collectors.toList()));
                break;
            case Protocol.DISCONNECT:
                // Extracting the name of one of the players that disconnected
                String disconnectedUsername = Protocol.clientDisconnectedExtract(line);

                System.out.println("Game handler client disconnected " + disconnectedUsername);

                // Removing the corresponding player that disconnected of the list of players in game
                Player disconnectedPlayer = this.game.getPlayers().stream()
                        .filter(player -> player.getUsername().equals(disconnectedUsername)).findFirst().get();

                this.game.removePlayer(disconnectedPlayer);

                // Sending gameover sequence to the other player (winner)
                Player winnerPlayer = this.game.getPlayers().get(0);
                String winnerUsername = winnerPlayer.getUsername();

                this.server.broadCastMessage(Protocol.gameOverFormat(Protocol.DISCONNECT, winnerUsername), winnerUsername);
                this.server.cleanUpGameRoom(disconnectedUsername, winnerUsername);

                break;
            default:
                // Unsupported command, 'do nothing'
        }
    }
}
