package server;

import game.BoardGame;
import game.OthelloGame;
import game.board.BoardMark;
import game.players.HumanPlayer;
import networking.Protocol;

import java.io.PipedReader;
import java.util.List;

/**
 * Runnable that handles the server queue of clients waiting to be added in a new game
 */
public class QueueHandler implements Runnable {
    /**
     * Holds the reference to the server
     */
    private Server server;

    /**
     * Initializes server reference
     * @param server
     */
    public QueueHandler(Server server) {
        this.server = server;
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        // Server queue reference
        List<String> serverQueue = this.server.getQueue();

        synchronized (serverQueue) {
            // A match room can be created only if atleast 2 players are in the queue,
            // putting the thread to a sleeping state and awaiting being notified
            while (serverQueue.size() < 2) {
                try {
                    serverQueue.wait();
                } catch (InterruptedException e) {
                    // TODO: Handle the exception
                }
            }

            // There are atleast 2 clients, creating match rooms for all 2 player pairs
            for (int groupStartIndex = 0; groupStartIndex < serverQueue.size(); groupStartIndex += 2) {
                // It's possible that the amount of clients in the queue is odd (for example, 3 clients)
                if (groupStartIndex + 1 >= serverQueue.size()) continue;

                String firstClientUsername = serverQueue.get(groupStartIndex);
                String secondClientUsername = serverQueue.get(groupStartIndex + 1);

                // Creating a game room for the new game
                GameRoom gameRoom = new GameRoom(this.server, firstClientUsername, secondClientUsername);

                // Getting the client handlers of both clients
                ClientHandler firstClientHandler = this.server.getClientHandlersReverse().get(firstClientUsername);
                ClientHandler secondClientHandler = this.server.getClientHandlersReverse().get(secondClientUsername);

                // Keeping track of the rooms (used for ease of access, this way client handler will be able to
                // get back the reference to the pipe to write to for game rooms game handler)
                this.server.rooms.put(firstClientHandler, gameRoom);
                this.server.rooms.put(secondClientHandler, gameRoom);

                // Notifying both clients of this newly created game
                this.server.broadCastMessage(Protocol.newGameFormat(firstClientUsername, secondClientUsername),
                        firstClientUsername,
                        secondClientUsername);
            }

            // Updating the queue, if there were odd amount of clients waiting, we perceive this client,
            // otherwise we just make the queue empty
            if (serverQueue.size() % 2 > 0) {
                this.server.queue = serverQueue.subList(serverQueue.size() - 1, serverQueue.size());
            } else {
                this.server.queue.clear();
            }
        }
    }
}
