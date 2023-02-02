package server.handlers;

import networking.Protocol;
import server.GameRoom;
import server.Server;

import java.io.IOException;
import java.util.List;

/**
 * Runnable that handles the server queue of clients waiting to be added in a new game.
 */
public class QueueHandler implements Runnable {
    /**
     * Holds the reference to the server.
     */
    private final Server server;

    /**
     * Initializes server reference.
     *
     * @param server Server instance
     */
    public QueueHandler(Server server) {
        this.server = server;
    }

    private void handleQueue(List<String> serverQueue) {
        // There are at least 2 clients, creating match rooms for all 2 player pairs
        for (int groupStartIndex = 0; groupStartIndex < serverQueue.size(); groupStartIndex += 2) {
            // It's possible that the amount of clients in the queue is odd (for example, 3 clients)
            if (groupStartIndex + 1 >= serverQueue.size()) {
                continue;
            }

            String firstClientUsername = serverQueue.get(groupStartIndex);
            String secondClientUsername = serverQueue.get(groupStartIndex + 1);

            // Creating a game room for the new game
            GameRoom gameRoom;

            try {
                gameRoom = new GameRoom(this.server, firstClientUsername, secondClientUsername);
            } catch (IOException e) {
                continue;
            }

            // Getting the client handlers of both clients
            ClientHandler firstClientHandler = this.server.getClientHandlersReverse()
                .get(firstClientUsername);
            ClientHandler secondClientHandler = this.server.getClientHandlersReverse()
                .get(secondClientUsername);

            // Keeping track of the rooms (used for ease of access,
            // this way client handler will be able to
            // get back the reference to the pipe to write to for game rooms game handler)
            synchronized (this.server.getRooms()) {
                this.server.setRooms(firstClientHandler, gameRoom);
                this.server.setRooms(secondClientHandler, gameRoom);
            }

            // Clearing up space in the queue
            this.server.setQueue(firstClientHandler);
            this.server.setQueue(secondClientHandler);

            // Notifying both clients of this newly created game
            this.server.broadCastMessage(
                Protocol.newGameFormat(firstClientUsername, secondClientUsername),
                    firstClientUsername,
                    secondClientUsername);
        }
    }

    /**
     * Runs this operation.
     */
    @Override
    public void run() {
        while (this.server.isRunning()) {
            synchronized (this.server.getQueue()) {
                // Server queue reference
                List<String> serverQueue = this.server.getQueue();

                // A match room can be created only if at least 2 players are in the queue,
                // putting the thread to a sleeping state and awaiting being notified
                while (serverQueue.size() < 2) {
                    try {
                        serverQueue.wait();
                    } catch (InterruptedException e) {
                        Thread.currentThread().interrupt();
                    }
                }

                this.handleQueue(serverQueue);
            }
        }
    }
}
